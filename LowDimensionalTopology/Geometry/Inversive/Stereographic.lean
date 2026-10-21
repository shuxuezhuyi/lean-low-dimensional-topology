/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Inversive.Inversions
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Stereographic projection and chordal topology

The ambient spaces use the Euclidean L² norm in dimensions n and n+1.
The canonical embedding appends a zero as the last coordinate. The sphere
homeomorphism is calibrated to coordinates: Mathlib's intermediate
hyperplane coordinate is twice the coordinate used here.

The chordal metric is pulled back from the actual unit sphere, with its
original `OnePoint` topology retained. Finite-pair and finite-to-infinity
distance formulas, topological compatibility on finite points, and global reflection
homeomorphisms are proved on these same structures.
-/

@[expose] public section
noncomputable section
open scoped Topology RealInnerProductSpace OnePoint
open EuclideanGeometry Filter Topology Metric
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}
/-- append a zero last coordinate as a linear isometry. -/
def equatorialEmbedding (n : ℕ) : Euclidean n →ₗᵢ[ℝ] Euclidean (n + 1) where
  toFun x := WithLp.toLp 2 (Fin.snoc x 0)
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' r x := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_castSucc]
    simp

/-- The last standard basis vector in dimension n+1. -/
def northPole (n : ℕ) : Euclidean (n + 1) := EuclideanSpace.single (Fin.last n) 1
/-- The north pole has unit Euclidean norm. -/
@[simp] theorem norm_northPole (n : ℕ) : ‖northPole n‖ = 1 := by simp [northPole]

/-- The canonical embedded Euclidean space is orthogonal to the north pole. -/
theorem equatorialEmbedding_mem (x : Euclidean n) :
    equatorialEmbedding n x ∈ (ℝ ∙ northPole n)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [northPole, equatorialEmbedding, EuclideanSpace.inner_single_left]

/-- The canonical isometry with codomain restricted to the equatorial hyperplane. -/
def equatorialEmbeddingToHyperplane (n : ℕ) : Euclidean n →ₗᵢ[ℝ] (ℝ ∙ northPole n)ᗮ where
  toLinearMap := (equatorialEmbedding n).toLinearMap.codRestrict _ equatorialEmbedding_mem
  norm_map' := (equatorialEmbedding n).norm_map

/-- The finite Euclidean space is isometric to the full equatorial hyperplane. -/
def equatorialEquiv (n : ℕ) : Euclidean n ≃ₗᵢ[ℝ] (ℝ ∙ northPole n)ᗮ :=
  LinearIsometryEquiv.ofSurjective
    (equatorialEmbeddingToHyperplane n) (by
      intro y
      refine ⟨WithLp.toLp 2 (fun i : Fin n ↦ (y : Euclidean (n + 1)) i.castSucc), ?_⟩
      apply Subtype.ext
      ext i
      change Fin.snoc (α := fun _ : Fin (n + 1) ↦ ℝ) (fun j : Fin n ↦ (y : Euclidean (n + 1)) j.castSucc) 0 i =
        (y : Euclidean (n + 1)) i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · have hy := y.property
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy
        simpa [northPole, EuclideanSpace.inner_single_left] using hy.symm
      · simp)

/-- The calibrated stereographic homeomorphism onto the unit n-sphere. -/
def stereographicHomeomorph (n : ℕ) :
    ExtendedEuclidean n ≃ₜ Metric.sphere (0 : Euclidean (n + 1)) 1 :=
  (((equatorialEquiv n).toHomeomorph.trans
    (Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num))).onePointCongr).trans
      (onePointHyperplaneHomeoUnitSphere (norm_northPole n))

/-- infinity is sent to the north pole. -/
theorem stereographicHomeomorph_infty (n : ℕ) :
    (stereographicHomeomorph n ∞ : Euclidean (n + 1)) = northPole n := by
  simp [stereographicHomeomorph, onePointHyperplaneHomeoUnitSphere]

/-- The finite stereographic formula in vector form. -/
theorem stereographicHomeomorph_coe (x : Euclidean n) :
    (stereographicHomeomorph n x : Euclidean (n + 1)) =
      (‖x‖ ^ 2 + 1)⁻¹ • ((2 : ℝ) • equatorialEmbedding n x +
        (‖x‖ ^ 2 - 1) • northPole n) := by
  have hraw : (stereographicHomeomorph n x : Euclidean (n + 1)) =
      stereoInvFunAux (northPole n) ((2 : ℝ) • equatorialEmbedding n x) := rfl
  rw [hraw, stereoInvFunAux_apply]
  simp only [norm_smul, Real.norm_eq_abs, (by norm_num : |(2 : ℝ)| = 2),
    (equatorialEmbedding n).norm_map, mul_pow]
  have hq : ‖x‖ ^ 2 + 1 ≠ 0 := by positivity
  have hq4 : 2 ^ 2 * ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  match_scalars <;> field_simp <;> ring

/-- The canonical embedding extended by fixing infinity. -/
def extendedEquatorialEmbedding (n : ℕ) : ExtendedEuclidean n → ExtendedEuclidean (n + 1) :=
  OnePoint.map (equatorialEmbedding n)
/-- The canonical embedding fixes infinity. -/
@[simp] theorem extendedEquatorialEmbedding_infty (n : ℕ) :
    extendedEquatorialEmbedding n ∞ = ∞ := rfl
/-- The extended embedding restricts to the canonical finite embedding. -/
@[simp] theorem extendedEquatorialEmbedding_coe (x : Euclidean n) :
    extendedEquatorialEmbedding n x = (equatorialEmbedding n x : ExtendedEuclidean (n + 1)) := rfl

/-- The extended canonical embedding is injective. -/
theorem extendedEquatorialEmbedding_injective (n : ℕ) :
    Function.Injective (extendedEquatorialEmbedding n) := by
  intro z w h
  induction z using OnePoint.rec <;> induction w using OnePoint.rec
  · rfl
  · simp at h
  · simp at h
  · apply congrArg OnePoint.some
    apply (equatorialEmbedding n).injective
    exact OnePoint.coe_injective h

/-- The canonical embedding retains each original coordinate. -/
@[simp] theorem equatorialEmbedding_castSucc (x : Euclidean n) (i : Fin n) :
    equatorialEmbedding n x i.castSucc = x i := by simp [equatorialEmbedding]
/-- The last coordinate of the canonical embedding is zero. -/
@[simp] theorem equatorialEmbedding_last (x : Euclidean n) :
    equatorialEmbedding n x (Fin.last n) = 0 := by simp [equatorialEmbedding]

/-- each of the first n stereographic coordinates. -/
theorem stereographicHomeomorph_coordinate (x : Euclidean n) (i : Fin n) :
    (stereographicHomeomorph n x : Euclidean (n + 1)) i.castSucc =
      2 * x i / (‖x‖ ^ 2 + 1) := by
  rw [stereographicHomeomorph_coe]
  simp [equatorialEmbedding, northPole, div_eq_mul_inv, mul_comm]

/-- The final stereographic coordinate. -/
theorem stereographicHomeomorph_last (x : Euclidean n) :
    (stereographicHomeomorph n x : Euclidean (n + 1)) (Fin.last n) =
      (‖x‖ ^ 2 - 1) / (‖x‖ ^ 2 + 1) := by
  rw [stereographicHomeomorph_coe]
  simp [equatorialEmbedding, northPole, div_eq_mul_inv, mul_comm]

/-- equation: distance transported from the unit sphere. -/
abbrev chordalDist (z w : ExtendedEuclidean n) : ℝ :=
  dist (stereographicHomeomorph n z) (stereographicHomeomorph n w)

/-- The sphere-induced metric with the original OnePoint topology. -/
abbrev chordalMetricSpace (n : ℕ) : MetricSpace (ExtendedEuclidean n) :=
  (stereographicHomeomorph n).isEmbedding.comapMetricSpace _

/-- The chordal metric induces exactly the one-point compactification topology. -/
theorem chordalMetricSpace_topology (n : ℕ) :
    (chordalMetricSpace n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (ExtendedEuclidean n)) := rfl

/-- The bundled metric has the declared chordal distance. -/
theorem chordalMetricSpace_dist (z w : ExtendedEuclidean n) :
    @dist (ExtendedEuclidean n) (chordalMetricSpace n).toDist z w = chordalDist z w := rfl

/-- The chordal metric restricted to the finite Euclidean space. -/
abbrev finiteChordalMetricSpace (n : ℕ) : MetricSpace (Euclidean n) := by
  let := chordalMetricSpace n
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.comapMetricSpace _

/-- restricted chordal and Euclidean metrics induce the same topology. -/
theorem finiteChordalMetricSpace_topology (n : ℕ) :
    (finiteChordalMetricSpace n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (Euclidean n)) := rfl

/-- The restricted metric uses the same chordal distance between finite points. -/
theorem finiteChordalMetricSpace_dist (x y : Euclidean n) :
    @dist (Euclidean n) (finiteChordalMetricSpace n).toDist x y =
      chordalDist (x : ExtendedEuclidean n) (y : ExtendedEuclidean n) := rfl

/-- Every stereographic image has unit Euclidean norm. -/
theorem norm_stereographicHomeomorph (z : ExtendedEuclidean n) :
    ‖(stereographicHomeomorph n z : Euclidean (n + 1))‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using (stereographicHomeomorph n z).property

/-- The embedded finite point is perpendicular to the north pole. -/
@[simp] theorem inner_equatorialEmbedding_northPole (x : Euclidean n) :
    inner ℝ (equatorialEmbedding n x) (northPole n) = 0 := by
  simp [equatorialEmbedding, northPole, EuclideanSpace.inner_single_right]
/-- The north pole is perpendicular to the embedded finite point. -/
@[simp] theorem inner_northPole_equatorialEmbedding (x : Euclidean n) :
    inner ℝ (northPole n) (equatorialEmbedding n x) = 0 := by
  rw [real_inner_comm, inner_equatorialEmbedding_northPole]

/-- An inner-product identity for the stereographic distance computation. -/
theorem inner_stereographicHomeomorph (x y : Euclidean n) :
    inner ℝ (stereographicHomeomorph n x : Euclidean (n + 1))
      (stereographicHomeomorph n y : Euclidean (n + 1)) =
    (‖x‖ ^ 2 + 1)⁻¹ * (‖y‖ ^ 2 + 1)⁻¹ *
      (4 * inner ℝ x y + (‖x‖ ^ 2 - 1) * (‖y‖ ^ 2 - 1)) := by
  rw [stereographicHomeomorph_coe, stereographicHomeomorph_coe]
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    inner_add_left, inner_add_right, inner_equatorialEmbedding_northPole,
    inner_northPole_equatorialEmbedding, mul_zero,
    real_inner_self_eq_norm_sq, norm_northPole, one_pow, mul_one,
    (equatorialEmbedding n).inner_map_map, zero_add, add_zero]
  ring

/-- equation: chordal distance between two finite points. -/
theorem chordalDist_coe_coe (x y : Euclidean n) :
    chordalDist (x : ExtendedEuclidean n) (y : ExtendedEuclidean n) =
      2 * dist x y / (Real.sqrt (1 + ‖x‖ ^ 2) * Real.sqrt (1 + ‖y‖ ^ 2)) := by
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hy : 0 < 1 + ‖y‖ ^ 2 := by positivity
  apply (sq_eq_sq₀ dist_nonneg (by positivity)).mp
  change dist (stereographicHomeomorph n x : Euclidean (n + 1))
    (stereographicHomeomorph n y : Euclidean (n + 1)) ^ 2 = _
  rw [dist_eq_norm, norm_sub_sq_real, norm_stereographicHomeomorph,
    norm_stereographicHomeomorph, inner_stereographicHomeomorph,
    div_pow, mul_pow, mul_pow, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le,
    dist_eq_norm, norm_sub_sq_real]
  have hx' : ‖x‖ ^ 2 + 1 ≠ 0 := by positivity
  have hy' : ‖y‖ ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- equation: chordal distance from a finite point to infinity. -/
theorem chordalDist_coe_infty (x : Euclidean n) :
    chordalDist (x : ExtendedEuclidean n) ∞ = 2 / Real.sqrt (1 + ‖x‖ ^ 2) := by
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  apply (sq_eq_sq₀ dist_nonneg (by positivity)).mp
  change dist (stereographicHomeomorph n x : Euclidean (n + 1))
    (stereographicHomeomorph n ∞ : Euclidean (n + 1)) ^ 2 = _
  rw [dist_eq_norm, norm_sub_sq_real, norm_stereographicHomeomorph,
    norm_stereographicHomeomorph, stereographicHomeomorph_infty,
    stereographicHomeomorph_coe]
  simp only [inner_smul_left, RCLike.conj_to_real, inner_add_left,
    inner_smul_left, inner_equatorialEmbedding_northPole,
    real_inner_self_eq_norm_sq, norm_northPole, one_pow, mul_zero, zero_add, mul_one]
  rw [div_pow, Real.sq_sqrt hx.le]
  have hx' : ‖x‖ ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The distance from infinity to itself is zero. -/
@[simp] theorem chordalDist_infty_infty (n : ℕ) :
    chordalDist (∞ : ExtendedEuclidean n) ∞ = 0 := dist_self _



/-- sphere inversion is continuous at the center mapped to infinity. -/
theorem continuousAt_sphereInversion_center (c : Euclidean n) {r : ℝ} (hr : r ≠ 0) :
    ContinuousAt (sphereInversion c r) (c : ExtendedEuclidean n) := by
  rw [OnePoint.continuousAt_coe, continuousAt_iff_punctured_nhds]
  simp only [Function.comp_def, sphereInversion_center]
  have hlim := OnePoint.tendsto_coe_infty (X := Euclidean n)
  rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at hlim
  apply (hlim.comp (tendsto_inversion_nhdsNE_center_cobounded hr)).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (sphereInversion_coe c r hx).symm

/-- Finite inversion approaches the center when its input tends to infinity. -/
theorem tendsto_inversion_cobounded_center (c : Euclidean n) (r : ℝ) :
    Tendsto (inversion c r) (Bornology.cobounded (Euclidean n)) (𝓝 c) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp_rw [dist_inversion_center]
  exact tendsto_const_nhds.div_atTop (tendsto_dist_right_cobounded_atTop c)

/-- sphere inversion is continuous at infinity. -/
theorem continuousAt_sphereInversion_infty (c : Euclidean n) (r : ℝ) :
    ContinuousAt (sphereInversion c r) (∞ : ExtendedEuclidean n) := by
  rw [OnePoint.continuousAt_infty', sphereInversion_infty,
    coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  apply (OnePoint.continuous_coe.tendsto c |>.comp
    (tendsto_inversion_cobounded_center c r)).congr'
  have hne : ∀ᶠ x : Euclidean n in Bornology.cobounded (Euclidean n), x ≠ c := by
    rw [Metric.cobounded_eq_cocompact]
    exact (isCompact_singleton : IsCompact ({c} : Set (Euclidean n))).compl_mem_cocompact
  filter_upwards [hne] with x hx
  exact (sphereInversion_coe c r hx).symm

/-- sphere inversion is continuous on the entire compactification. -/
theorem continuous_sphereInversion (c : Euclidean n) {r : ℝ} (hr : r ≠ 0) :
    Continuous (sphereInversion c r) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  induction z using OnePoint.rec with
  | infty => exact continuousAt_sphereInversion_infty c r
  | coe x =>
    by_cases hx : x = c
    · subst x; exact continuousAt_sphereInversion_center c hr
    · rw [OnePoint.continuousAt_coe]
      apply ContinuousAt.congr_of_eventuallyEq
        (OnePoint.continuous_coe.continuousAt.comp
          (continuousAt_const.inversion continuousAt_const continuousAt_id hx))
      filter_upwards [eventually_ne_nhds hx] with y hy
      exact sphereInversion_coe c r hy

/-- sphere inversion as a homeomorphism, including both exceptional points. -/
def sphereInversionHomeomorph (c : Euclidean n) (r : ℝ) (hr : r ≠ 0) :
    ExtendedEuclidean n ≃ₜ ExtendedEuclidean n where
  toEquiv := (sphereInversion_involutive c hr).toPerm (sphereInversion c r)
  continuous_toFun := continuous_sphereInversion c hr
  continuous_invFun := continuous_sphereInversion c hr

/-- The finite plane-reflection formula as a Euclidean homeomorphism. -/
def planeReflectionFiniteHomeomorph (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    Euclidean n ≃ₜ Euclidean n where
  toEquiv := (planeReflectionFinite_involutive a t ha).toPerm (planeReflectionFinite a t)
  continuous_toFun := by unfold planeReflectionFinite; fun_prop
  continuous_invFun := by unfold planeReflectionFinite; fun_prop

/-- plane reflection as a homeomorphism fixing infinity. -/
def planeReflectionHomeomorph (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    ExtendedEuclidean n ≃ₜ ExtendedEuclidean n :=
  (planeReflectionFiniteHomeomorph a t ha).onePointCongr

/-- The bundled plane homeomorphism agrees with the earlier reflection. -/
theorem planeReflectionHomeomorph_apply (a : Euclidean n) (t : ℝ) (ha : a ≠ 0)
    (z : ExtendedEuclidean n) : planeReflectionHomeomorph a t ha z = planeReflection a t z := by
  induction z using OnePoint.rec <;> rfl

/-- The bundled sphere homeomorphism agrees with the earlier inversion. -/
theorem sphereInversionHomeomorph_apply (c : Euclidean n) (r : ℝ) (hr : r ≠ 0)
    (z : ExtendedEuclidean n) : sphereInversionHomeomorph c r hr z = sphereInversion c r z := rfl

/-- plane reflection is continuous everywhere on the compactification. -/
theorem continuous_planeReflection (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    Continuous (planeReflection a t) := by
  exact (planeReflectionHomeomorph a t ha).continuous.congr
    (planeReflectionHomeomorph_apply a t ha)

/-- The canonical image is precisely the last-coordinate-zero hyperplane. -/
theorem equatorialEmbedding_range (n : ℕ) :
    Set.range (equatorialEmbedding n) =
      {y : Euclidean (n + 1) | y (Fin.last n) = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact equatorialEmbedding_last x
  · intro hy
    refine ⟨WithLp.toLp 2 (fun i : Fin n ↦ y i.castSucc), ?_⟩
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [equatorialEmbedding] using hy.symm
    · simp [equatorialEmbedding]

/-- The extended canonical image is precisely the extended equatorial plane. -/
theorem extendedEquatorialEmbedding_range (n : ℕ) :
    Set.range (extendedEquatorialEmbedding n) = plane (northPole n) 0 := by
  ext z
  change (∃ w, extendedEquatorialEmbedding n w = z) ↔
    z = ∞ ∨ ∃ y : Euclidean (n + 1), inner ℝ y (northPole n) = 0 ∧ (y : ExtendedEuclidean (n + 1)) = z
  constructor
  · rintro ⟨w, hw⟩
    induction w using OnePoint.rec with
    | infty => left; exact hw.symm
    | coe x =>
      right
      exact ⟨equatorialEmbedding n x, inner_equatorialEmbedding_northPole x, hw⟩
  · rintro (hinfty | ⟨y, hy, hcoe⟩)
    · subst z; exact ⟨∞, rfl⟩
    · have hy0 : y (Fin.last n) = 0 := by
        simpa [northPole, EuclideanSpace.inner_single_right] using hy
      have hyRange : y ∈ Set.range (equatorialEmbedding n) := by
        rw [equatorialEmbedding_range]; exact hy0
      obtain ⟨x, hx⟩ := hyRange
      refine ⟨(x : ExtendedEuclidean n), ?_⟩
      rw [extendedEquatorialEmbedding_coe, hx]
      exact hcoe

/-- extended Euclidean space maps bijectively onto the unit n-sphere. -/
theorem stereographicHomeomorph_bijective (n : ℕ) :
    Function.Bijective (stereographicHomeomorph n) := (stereographicHomeomorph n).bijective

/-- By construction, stereographic projection is an isometry for the chordal metric. -/
theorem stereographic_isometry (n : ℕ) :
    letI := chordalMetricSpace n
    Isometry (stereographicHomeomorph n) := by
  let := chordalMetricSpace n
  exact Isometry.of_dist_eq (fun _ _ ↦ rfl)

/-- sphere inversion is a homeomorphism for the chordal metric. -/
theorem sphereInversion_isHomeomorph_chordal (c : Euclidean n) (r : ℝ) (hr : r ≠ 0) :
    letI := chordalMetricSpace n
    IsHomeomorph (sphereInversion c r) := by
  let := chordalMetricSpace n
  exact (sphereInversionHomeomorph c r hr).isHomeomorph

/-- plane reflection is a homeomorphism for the chordal metric. -/
theorem planeReflection_isHomeomorph_chordal (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    letI := chordalMetricSpace n
    IsHomeomorph (planeReflection a t) := by
  let := chordalMetricSpace n
  exact (planeReflectionHomeomorph a t ha).isHomeomorph

end LowDimensionalTopology.Geometry.Inversive
