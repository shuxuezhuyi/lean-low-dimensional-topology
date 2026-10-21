/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HyperbolicBalls
public import LowDimensionalTopology.Geometry.Surfaces.Topology.FinitePunctureExtension

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
local instance nativePuncturedDiscMetric : MetricSpace 𝔻 := discHyperbolicMetric

/-- A physical disc ball about zero is the genuine Euclidean norm cut. -/
theorem disc_mem_ball_zero_iff_norm_lt_tanh (z : 𝔻) (r : ℝ) :
    z ∈ Metric.ball (0 : 𝔻) r ↔ ‖(z : ℂ)‖ < Real.tanh (r / 2) := by
  rw [Metric.mem_ball, dist_comm, discHyperbolicMetric_distance,
    disc_norm_eq_tanh_half_distance]
  have h := Real.artanh_lt_artanh_iff
    ⟨Real.neg_one_lt_tanh (discPathDist 0 z / 2), Real.tanh_lt_one _⟩
    ⟨Real.neg_one_lt_tanh (r / 2), Real.tanh_lt_one _⟩
  rw [Real.artanh_tanh, Real.artanh_tanh] at h
  exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).symm.trans h

/-- The actual finite-coordinate image of a punctured native disc ball. -/
theorem disc_punctured_ball_zero_coe_image (r : ℝ) :
    ((↑) : 𝔻 → ℂ) '' (Metric.ball (0 : 𝔻) r \ {0}) =
      Metric.ball (0 : ℂ) (Real.tanh (r / 2)) \ {0} := by
  ext z
  constructor
  · rintro ⟨w, ⟨hw, hn⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right] using
        (disc_mem_ball_zero_iff_norm_lt_tanh w r).mp hw
    · intro h
      apply hn
      apply Subtype.ext
      change (w : ℂ) = 0
      exact h
  · rintro ⟨hz, hn⟩
    have hnorm : ‖z‖ < Real.tanh (r / 2) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    let w : 𝔻 := Complex.UnitDisc.mk z (hnorm.trans (Real.tanh_lt_one _))
    refine ⟨w, ⟨(disc_mem_ball_zero_iff_norm_lt_tanh w r).mpr hnorm, ?_⟩, rfl⟩
    intro h
    apply hn
    exact congrArg (fun y : 𝔻 => (y : ℂ)) h

/-- A punctured genuine disc ball is preconnected, for every radius. -/
theorem disc_punctured_ball_zero_isPreconnected (r : ℝ) :
    IsPreconnected (Metric.ball (0 : 𝔻) r \ {0}) := by
  by_cases hr : 0 < r
  · have ht : 0 < Real.tanh (r / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
    apply Complex.UnitDisc.isEmbedding_coe.toIsInducing.isPreconnected_image.mp
    rw [disc_punctured_ball_zero_coe_image]
    exact _root_.LowDimensionalTopology.Geometry.Surfaces.complex_punctured_ball_preconnected 0 _ ht
  · rw [Metric.ball_eq_empty.mpr (le_of_not_gt hr), empty_sdiff]
    exact isPreconnected_empty

/-- Removing the center from any actual native hyperbolic ball preserves
preconnectedness. The native metric and its original topology are retained. -/
theorem native_punctured_ball_isPreconnected (x : ℍ) (r : ℝ) :
    IsPreconnected (Metric.ball x r \ {x}) := by
  let e := cayleyHomeomorph.trans (discOriginNormalizer (halfPlaneToDisc x))
  have he : Isometry e := (discOriginNormalizer_isometry (halfPlaneToDisc x)).comp cayley_isometry
  have hx : e x = 0 := discOriginNormalizer_apply_self _
  have himage : e '' (Metric.ball x r \ {x}) = Metric.ball (0 : 𝔻) r \ {0} := by
    ext z
    constructor
    · rintro ⟨w, ⟨hw, hn⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · change dist (e w) 0 < r
        rw [← hx, he.dist_eq]
        exact hw
      · intro h
        apply hn
        exact e.injective (h.trans hx.symm)
    · rintro ⟨hz, hn⟩
      refine ⟨e.symm z, ⟨?_, ?_⟩, e.apply_symm_apply z⟩
      · change dist (e.symm z) x < r
        rw [← he.dist_eq, e.apply_symm_apply, hx]
        exact hz
      · intro h
        apply hn
        rw [← e.apply_symm_apply z, h, hx]
        rfl
  apply e.isEmbedding.toIsInducing.isPreconnected_image.mp
  rw [himage]
  exact disc_punctured_ball_zero_isPreconnected r

end LowDimensionalTopology.Geometry.Hyperbolic
