/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.RadialCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.Closed
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfSpaceBall

/-!
# Actual Klein coordinates in arbitrary real normed dimension
-/

@[expose] public section
open Set
open scoped UpperHalfPlane Topology RealInnerProductSpace Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]













theorem kleinRadialMap_boundary_fixed {x : E} (hx : ‖x‖ = 1) : kleinRadialMap x = x := by
  norm_num [kleinRadialMap,hx]




theorem kleinRadialMap_complex (z : ℂ) : kleinRadialMap z = kleinFormula z := by
  rfl


section InnerProduct
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem kleinRadialMap_sphere_iff (c x : F) (r : ℝ) (hr : 0 < r)
    (hc : ‖c‖ ^ 2 = 1 + r ^ 2) :
    dist x c = r ↔ inner ℝ (kleinRadialMap x) c = 1 := by
  have hden : 1 + ‖x‖ ^ 2 ≠ 0 := by positivity
  have he : inner ℝ (kleinRadialMap x) c = 1 ↔ 2 * inner ℝ x c = 1 + ‖x‖ ^ 2 := by
    rw [kleinRadialMap,real_inner_smul_left,div_mul_eq_mul_div,div_eq_one_iff_eq hden]
  rw [he,dist_eq_norm]
  have hn := norm_sub_sq_real x c
  constructor
  · intro hx
    have hxs := congrArg (fun t : ℝ => t ^ 2) hx
    nlinarith
  · intro hx
    apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
    nlinarith

theorem kleinRadialMap_image_orthogonal_sphere (c : F) (r : ℝ) (hr : 0 < r)
    (hc : ‖c‖ ^ 2 = 1 + r ^ 2) :
    kleinRadialMap '' (Metric.sphere c r ∩ Metric.closedBall (0 : F) 1) =
      {y : F | inner ℝ y c = 1} ∩ Metric.closedBall (0 : F) 1 := by
  apply subset_antisymm
  · rintro y ⟨x,⟨hx,hxb⟩,rfl⟩
    exact ⟨(kleinRadialMap_sphere_iff c x r hr hc).mp hx,kleinRadialMap_mem_closedBall x⟩
  · intro y hy
    let x := inverseKleinRadialMap y
    have hxb : x ∈ Metric.closedBall (0 : F) 1 := inverseKleinRadialMap_mem_closedBall hy.2
    have he : kleinRadialMap x = y := kleinRadialMap_inverseKleinRadialMap hy.2
    refine ⟨x,⟨?_,hxb⟩,he⟩
    apply (kleinRadialMap_sphere_iff c x r hr hc).mpr
    rw [he]
    exact hy.1

theorem kleinRadialMap_image_open_orthogonal_sphere (c : F) (r : ℝ) (hr : 0 < r)
    (hc : ‖c‖ ^ 2 = 1 + r ^ 2) :
    kleinRadialMap '' (Metric.sphere c r ∩ Metric.ball (0 : F) 1) =
      {y : F | inner ℝ y c = 1} ∩ Metric.ball (0 : F) 1 := by
  apply subset_antisymm
  · rintro y ⟨x,⟨hx,hxb⟩,rfl⟩
    exact ⟨(kleinRadialMap_sphere_iff c x r hr hc).mp hx,kleinRadialMap_mem_ball hxb⟩
  · intro y hy
    let x := inverseKleinRadialMap y
    have hxb : x ∈ Metric.ball (0 : F) 1 := inverseKleinRadialMap_mem_ball hy.2
    have he : kleinRadialMap x = y := kleinRadialMap_inverseKleinRadialMap (Metric.ball_subset_closedBall hy.2)
    refine ⟨x,⟨?_,hxb⟩,he⟩
    apply (kleinRadialMap_sphere_iff c x r hr hc).mpr
    rw [he]
    exact hy.1

theorem kleinRadialMap_orthogonal_sphere_boundary (c : F) (r : ℝ) (hr : 0 < r)
    (hc : ‖c‖ ^ 2 = 1 + r ^ 2) :
    Metric.sphere c r ∩ Metric.sphere (0 : F) 1 =
      {y : F | inner ℝ y c = 1} ∩ Metric.sphere (0 : F) 1 := by
  ext x
  constructor
  · rintro ⟨hx,hxb⟩
    have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hxb
    have he := (kleinRadialMap_sphere_iff c x r hr hc).mp hx
    exact ⟨by rwa [kleinRadialMap_boundary_fixed hxnorm] at he,hxb⟩
  · rintro ⟨hx,hxb⟩
    refine ⟨?_,hxb⟩
    apply (kleinRadialMap_sphere_iff c x r hr hc).mpr
    rwa [kleinRadialMap_boundary_fixed (mem_sphere_zero_iff_norm.mp hxb)]

end InnerProduct


/-- The actual Klein disc metric transported from the already verified Poincaré path metric.
Its topology remains the actual open-disc subspace topology. -/
@[instance_reducible] def kleinDiscMetric : MetricSpace 𝔻 := by
  let := discHyperbolicMetric
  exact Topology.IsEmbedding.comapMetricSpace kleinToPoincare kleinHomeomorph.symm.isEmbedding

theorem kleinDiscMetric_distance (z w : 𝔻) :
    @dist 𝔻 kleinDiscMetric.toDist z w = discPathDist (kleinToPoincare z) (kleinToPoincare w) := by
  change dist (discToHalfPlane (kleinToPoincare z)) (discToHalfPlane (kleinToPoincare w)) = _
  exact (discPathDist_eq_halfPlane _ _).symm

theorem kleinDiscMetric_poincare_isometry :
    @Isometry 𝔻 𝔻 discHyperbolicMetric.toPseudoEMetricSpace kleinDiscMetric.toPseudoEMetricSpace
      poincareToKlein := by
  intro z w
  change edist (discToHalfPlane (kleinToPoincare (poincareToKlein z)))
    (discToHalfPlane (kleinToPoincare (poincareToKlein w))) =
      edist (discToHalfPlane z) (discToHalfPlane w)
  rw [kleinToPoincare_poincareToKlein,kleinToPoincare_poincareToKlein]

/-- The genuine Poincaré h-line becomes a genuine affine chord in the actual Klein disc. -/
def kleinDiscLineCarrier (L : DiscLine) : Set 𝔻 := poincareToKlein '' L.carrier

theorem kleinDiscLineCarrier_affine (L : DiscLine) :
    ∃ (a : ℂ) (t : ℝ), a ≠ 0 ∧ kleinDiscLineCarrier L = {z : 𝔻 | inner ℝ (z : ℂ) a = t} := by
  obtain ⟨a,t,ha,he⟩ := L.exists_klein_affine_equation
  refine ⟨a,t,ha,?_⟩
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (he z).mp hz
  · intro hw
    refine ⟨kleinToPoincare w,?_,poincareToKlein_kleinToPoincare w⟩
    apply (he _).mpr
    change inner ℝ (w : ℂ) a = t at hw
    simpa only [poincareToKlein_kleinToPoincare] using hw

theorem kleinDiscLineCarrier_closed_chord (L : DiscLine) :
    closure (discToClosedModel '' kleinDiscLineCarrier L) = closedPoincareToKlein '' L.closedCarrier := by
  change closure (discToClosedModel '' kleinDiscLineCarrier L) =
    closedKleinHomeomorph '' closure (discToClosedModel '' L.carrier)
  rw [closedKleinHomeomorph.image_closure]
  rw [kleinDiscLineCarrier,image_image,image_image]
  congr 1

theorem kleinDiscLineCarrier_ideal_fixed (L : DiscLine) (p : 𝕔𝔻) (hp : ‖(p : ℂ)‖ = 1) :
    p ∈ closure (discToClosedModel '' kleinDiscLineCarrier L) ↔ p ∈ L.closedCarrier := by
  rw [kleinDiscLineCarrier_closed_chord]
  have hf := closedPoincareToKlein_ideal_fixed p hp
  have hm : closedPoincareToKlein p ∈ closedPoincareToKlein '' L.closedCarrier ↔
      p ∈ L.closedCarrier := closedKleinHomeomorph.injective.mem_set_image
  rwa [hf] at hm

open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
variable {n : ℕ}

def verticalProjection (n : ℕ) : Inversive.Euclidean (n+1) →ₗ[ℝ] Inversive.Euclidean n where
  toFun x := WithLp.toLp 2 (fun i => x i.castSucc)
  map_add' x y := by ext i; rfl
  map_smul' r x := by ext i; rfl

theorem verticalProjection_equatorial (x : Inversive.Euclidean n) :
    verticalProjection n (Inversive.equatorialEmbedding n x) = x := by
  ext i
  exact Inversive.equatorialEmbedding_castSucc x i

theorem verticalProjection_north : verticalProjection n (Inversive.northPole n) = 0 := by
  ext i
  simp [verticalProjection,Inversive.northPole]

theorem verticalProjection_norm_sq (x : Inversive.Euclidean (n+1)) :
    ‖x‖ ^ 2 = ‖verticalProjection n x‖ ^ 2 + x (Fin.last n) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_castSucc]
  rfl

theorem equatorial_projection_decomposition (x : Inversive.Euclidean (n+1)) :
    Inversive.equatorialEmbedding n (verticalProjection n x) + x (Fin.last n) • Inversive.northPole n = x := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Inversive.northPole]
  · simp [verticalProjection,Inversive.northPole]


theorem kleinRadialMap_eq_vertical_stereographic (x : Inversive.Euclidean n) :
    verticalProjection n (Inversive.stereographicHomeomorph n (x : Inversive.ExtendedEuclidean n)).val =
      kleinRadialMap x := by
  rw [Inversive.stereographicHomeomorph_coe,map_smul,map_add,map_smul,map_smul,
    verticalProjection_equatorial,verticalProjection_north,smul_zero,add_zero,smul_smul]
  change ((‖x‖ ^ 2 + 1)⁻¹ * 2) • x = (2 / (1 + ‖x‖ ^ 2) : ℝ) • x
  congr 1
  ring

theorem verticalProjection_northPlane (x : Inversive.Euclidean (n+1)) :
    verticalProjection n (Inversive.planeReflectionFinite (Inversive.northPole n) 0 x) = verticalProjection n x := by
  rw [northPlane_finite_formula,map_sub,map_smul,verticalProjection_north,smul_zero,sub_zero]

theorem kleinRadialMap_eq_vertical_reflected_stereographic (x : Inversive.Euclidean n) :
    verticalProjection n (Inversive.planeReflectionFinite (Inversive.northPole n) 0
      (Inversive.stereographicHomeomorph n (x : Inversive.ExtendedEuclidean n)).val) = kleinRadialMap x := by
  rw [verticalProjection_northPlane,kleinRadialMap_eq_vertical_stereographic]

theorem kleinRadialMap_image_actual_orthogonal_sphere (c : Inversive.Euclidean n) (r : ℝ)
    (hr : 0 < r) (horth : Inversive.UnitSphereOrthogonal c r) :
    kleinRadialMap '' (Metric.sphere c r ∩ Metric.closedBall (0 : Inversive.Euclidean n) 1) =
      {y : Inversive.Euclidean n | inner ℝ y c = 1} ∩ Metric.closedBall (0 : Inversive.Euclidean n) 1 :=
  kleinRadialMap_image_orthogonal_sphere c r hr horth.norm_sq

theorem kleinRadialMap_actual_orthogonal_sphere_boundary (c : Inversive.Euclidean n) (r : ℝ)
    (hr : 0 < r) (horth : Inversive.UnitSphereOrthogonal c r) :
    Metric.sphere c r ∩ Metric.sphere (0 : Inversive.Euclidean n) 1 =
      {y : Inversive.Euclidean n | inner ℝ y c = 1} ∩ Metric.sphere (0 : Inversive.Euclidean n) 1 :=
  kleinRadialMap_orthogonal_sphere_boundary c r hr horth.norm_sq

end
end LowDimensionalTopology.Geometry.Hyperbolic
