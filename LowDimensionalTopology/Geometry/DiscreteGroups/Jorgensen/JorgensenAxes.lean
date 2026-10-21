module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenDisplacement
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius

/-- The genuine diagonal determinant-one action with eigenvalues `u` and `u⁻¹`. -/
def eigenvalueMobius (u : ℂ) (hu : u ≠ 0) : Mobius.complexMobiusGroup :=
  Mobius.affineMobius (u ^ 2) 0 (pow_ne_zero 2 hu)

/-- The genuine determinant-one diagonal representative. -/
def eigenvalueSpecialLinearLift (u : ℂ) (hu : u ≠ 0) : Auxiliary.Algebra.SpecialLinear2 :=
  ⟨!![u, 0; 0, u⁻¹], by simp [Matrix.det_fin_two, hu]⟩

/-- The actual full extended-plane projection of the diagonal representative is the eigenvalue model. -/
theorem eigenvalueSpecialLinearLift_projection (u : ℂ) (hu : u ≠ 0) :
    Mobius.mobiusSpecialLinearProjection (eigenvalueSpecialLinearLift u hu) = eigenvalueMobius u hu := by
  apply Mobius.complexMobiusEquivFractionalLinear.injective
  rw [Mobius.mobiusSpecialLinearProjection_equiv]
  change Mobius.matrixProjection (Matrix.SpecialLinearGroup.toGL (eigenvalueSpecialLinearLift u hu)) =
    Mobius.matrixProjection (Mobius.coefficientMatrix (u ^ 2) 0 0 1 (by simpa using pow_ne_zero 2 hu))
  apply (Mobius.matrixProjection_eq_iff _ _).mpr
  refine ⟨Units.mk0 u hu, ?_⟩
  apply Units.ext
  rw [Mobius.generalLinear_mul_scalar_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenvalueSpecialLinearLift, Matrix.SpecialLinearGroup.toGL, Mobius.coefficientMatrix_val, hu, pow_two]

/-- The source rotation term uses the argument of an eigenvalue. -/
def mobiusEigenvalueRotation (u : ℂ) : ℝ := Real.sin (Complex.arg u) ^ 2

/-- With the actual complex norm and argument. -/
theorem eigenvalue_rotation_identity (u : ℂ) (hu : u ≠ 0) :
    ‖u - u⁻¹‖ ^ 2 = (‖u‖ - ‖u‖⁻¹) ^ 2 + 4 * mobiusEigenvalueRotation u := by
  have hq : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [mobiusEigenvalueRotation, Complex.sin_arg, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq_eq_norm_sq]
  field_simp [hn]
  linear_combination -(‖u‖ ^ 2 - 1) ^ 2 * hq

/-- The affine lift acts on the actual interior by the diagonal similarity formula. -/
theorem eigenvalueMobius_smul (u : ℂ) (hu : u ≠ 0) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (eigenvalueMobius u hu • x).val = Hyperbolic.QuaternionHalfSpace.quaternionThreePoint
      (u ^ 2 * Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val) (‖u‖ ^ 2 *
        Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val) := by
  rw [eigenvalueMobius, Mobius.affineMobius_smul, norm_pow, add_zero]

/-- The half-displacement square is exactly the Euclidean difference divided by the two heights. -/
theorem mobiusSinhDisplacement_sq (f : Mobius.complexMobiusGroup) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    4 * mobiusSinhDisplacement f x ^ 2 =
      ‖x.val - (f • x).val‖ ^ 2 /
        (Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val * Hyperbolic.QuaternionHalfSpace.quaternionHeight
          (f • x).val) := by
  have ht : Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val ≠ 0 := x.property.ne'
  have hs : Hyperbolic.QuaternionHalfSpace.quaternionHeight (f • x).val ≠ 0 := (f • x).property.ne'
  have hc := Hyperbolic.QuaternionHalfSpace.parabolic_upperHalfSpacePathDist_cosh x (f • x)
  have hd := Real.cosh_two_mul (Mobius.upperHalfSpacePathDist x (f • x) / 2)
  rw [show 2 * (Mobius.upperHalfSpacePathDist x (f • x) / 2) =
    Mobius.upperHalfSpacePathDist x (f • x) by ring] at hd
  have hr := Real.cosh_sq_sub_sinh_sq (Mobius.upperHalfSpacePathDist x (f • x) / 2)
  unfold mobiusSinhDisplacement
  field_simp [ht, hs] at hc ⊢
  linear_combination hc - (2 * Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val *
    Hyperbolic.QuaternionHalfSpace.quaternionHeight (f • x).val) * hd -
    (2 * Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val * Hyperbolic.QuaternionHalfSpace.quaternionHeight
      (f • x).val) * hr

/-- The horizontal coefficient has the exact eigenvalue-difference norm. -/
theorem eigenvalue_horizontal_norm (u : ℂ) (hu : u ≠ 0) :
    ‖1 - u ^ 2‖ = ‖u‖ * ‖u - u⁻¹‖ := by
  rw [← norm_mul]
  have he : u * (u - u⁻¹) = u ^ 2 - 1 := by field_simp
  rw [he, norm_sub_rev]

/-- For the original hyperbolic path metric. -/
theorem eigenvalue_displacement_identity (u : ℂ) (hu : u ≠ 0) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    4 * mobiusSinhDisplacement (eigenvalueMobius u hu) x ^ 2 =
      (‖u‖ - ‖u‖⁻¹) ^ 2 +
        (‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ /
          Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val) ^ 2 * ‖u - u⁻¹‖ ^ 2 := by
  rw [mobiusSinhDisplacement_sq, eigenvalueMobius_smul, Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint]
  rw [← dist_eq_norm, Hyperbolic.QuaternionHalfSpace.horoball_distance_sq]
  have hz : Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val - u ^ 2 *
    Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val =
      (1 - u ^ 2) * Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val := by ring
  rw [hz, norm_mul, eigenvalue_horizontal_norm u hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have ht : Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val ≠ 0 := x.property.ne'
  field_simp [hn, ht]
  ring

local instance jorgensenAxesHyperbolicMetric : MetricSpace Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  upperHalfSpaceHyperbolicMetricSpace
local instance jorgensenAxesHyperbolicPseudoMetric : PseudoMetricSpace Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  upperHalfSpaceHyperbolicMetricSpace.toPseudoMetricSpace
local instance jorgensenAxesHyperbolicPseudoEMetric : PseudoEMetricSpace
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  upperHalfSpaceHyperbolicMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace

/-- The actual standard vertical geodesic in H3. -/
def mobiusVerticalGeodesic : Set Hyperbolic.QuaternionHalfSpace.UpperHalfSpace := {x |
    Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val = 0}

/-- In the genuine hyperbolic metric, the cosh distance to a vertical point has this coordinate form. -/
theorem mobiusVerticalPoint_cosh_distance (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (s : ℝ) (hs : 0 < s) :
    Real.cosh (dist x (Mobius.mobiusVerticalPoint s hs)) =
      (‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ ^ 2 +
        Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val ^ 2 + s ^ 2) /
        (2 * Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val * s) := by
  change Real.cosh (@dist Hyperbolic.QuaternionHalfSpace.UpperHalfSpace upperHalfSpaceHyperbolicMetricSpace.toDist
    x _) = _
  rw [upperHalfSpaceHyperbolicMetricSpace_dist, Hyperbolic.QuaternionHalfSpace.parabolic_upperHalfSpacePathDist_cosh]
  change 1 + ‖x.val - Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 s‖ ^ 2 /
    (2 * Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val * Hyperbolic.QuaternionHalfSpace.quaternionHeight
      (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 s)) = _
  rw [Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint, ← dist_eq_norm,
    Hyperbolic.QuaternionHalfSpace.horoball_distance_sq, sub_zero]
  have ht : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val := x.property
  field_simp [ht.ne', hs.ne']
  ring

/-- The perpendicular foot on the vertical geodesic has the actual Euclidean radial height. -/
def mobiusVerticalFoot (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  Mobius.mobiusVerticalPoint (Real.sqrt (‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ ^ 2 +
    Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val ^ 2))
    (Real.sqrt_pos.mpr (by
      nlinarith [sq_nonneg ‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖,
        show 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val from x.property]))

/-- The physical vertical foot lies on the physical complete geodesic. -/
theorem mobiusVerticalFoot_mem (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) : mobiusVerticalFoot x ∈
    mobiusVerticalGeodesic := by
  exact Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint 0 _

/-- The vertical foot gives the exact cosh of its genuine hyperbolic distance. -/
theorem mobiusVerticalFoot_cosh_distance (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Real.cosh (dist x (mobiusVerticalFoot x)) =
      Real.sqrt (‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ ^ 2 +
        Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val ^ 2) /
        Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val := by
  rw [mobiusVerticalFoot, mobiusVerticalPoint_cosh_distance]
  have hr := Real.sq_sqrt (by positivity : 0 ≤
    ‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ ^ 2 +
      Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val ^ 2)
  have hp : Real.sqrt (‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ ^ 2 +
    Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by
      nlinarith [sq_nonneg ‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖,
        show 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val from x.property]))
  have ht : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val := x.property
  field_simp [ht.ne', hp]
  nlinarith

/-- The vertical foot minimizes genuine distance over every point on the complete vertical geodesic. -/
theorem mobiusVerticalFoot_distance_le (x y : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (hy : y ∈
    mobiusVerticalGeodesic) :
    dist x (mobiusVerticalFoot x) ≤ dist x y := by
  have hty : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight y.val := y.property
  have htx : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val := x.property
  have he : y = Mobius.mobiusVerticalPoint (Hyperbolic.QuaternionHalfSpace.quaternionHeight y.val) hty := by
    apply Subtype.ext
    have h := Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates y.val
    rw [show Hyperbolic.QuaternionHalfSpace.quaternionHorizontal y.val = 0 from hy] at h
    exact h.symm
  rw [he]
  have hc : Real.cosh (dist x (mobiusVerticalFoot x)) ≤
      Real.cosh (dist x (Mobius.mobiusVerticalPoint (Hyperbolic.QuaternionHalfSpace.quaternionHeight y.val) hty)) := by
    rw [mobiusVerticalFoot_cosh_distance, mobiusVerticalPoint_cosh_distance]
    apply (div_le_div_iff₀ htx (by positivity : 0 <
      2 * Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val * Hyperbolic.QuaternionHalfSpace.quaternionHeight
        y.val)).mpr
    have hr := Real.sq_sqrt (by positivity : 0 ≤
      ‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ ^ 2 +
        Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val ^ 2)
    nlinarith [sq_nonneg (Hyperbolic.QuaternionHalfSpace.quaternionHeight y.val -
      Real.sqrt (‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ ^ 2 +
        Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val ^ 2))]
  simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hc

/-- Distance to the true vertical geodesic is attained at the true perpendicular foot. -/
theorem mobiusVerticalGeodesic_infDist (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Metric.infDist x mobiusVerticalGeodesic = dist x (mobiusVerticalFoot x) := by
  apply le_antisymm (Metric.infDist_le_dist_of_mem (mobiusVerticalFoot_mem x))
  exact (Metric.le_infDist ⟨mobiusVerticalFoot x, mobiusVerticalFoot_mem x⟩).mpr
    (fun _ hy => mobiusVerticalFoot_distance_le x _ hy)

/-- The distance-to-axis coordinate identity, with genuine metric infimum distance. -/
theorem mobiusVerticalGeodesic_sinh_infDist (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Real.sinh (Metric.infDist x mobiusVerticalGeodesic) =
      ‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ /
        Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val := by
  rw [mobiusVerticalGeodesic_infDist]
  have hc := mobiusVerticalFoot_cosh_distance x
  have ht : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val := x.property
  have hr := Real.cosh_sq_sub_sinh_sq (dist x (mobiusVerticalFoot x))
  have hs := Real.sq_sqrt (by positivity : 0 ≤
    ‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ ^ 2 +
      Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val ^ 2)
  apply (sq_eq_sq₀ (Real.sinh_nonneg_iff.mpr dist_nonneg)
    (div_nonneg (norm_nonneg _) x.property.le)).mp
  rw [hc] at hr
  field_simp [ht.ne'] at hr ⊢
  nlinarith

/-- The genuine geodesic determined by the boundary fixed pair, realized as an elliptic fixed axis.
The same endpoint pair determines the same set, including for loxodromic maps. -/
def mobiusGeodesicAxis (f : Mobius.complexMobiusGroup) : Set Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  {x | ∃ h : Mobius.complexMobiusGroup, Mobius.MobiusElliptic h ∧ Mobius.MobiusSameFixedPoints h f ∧ x ∈
    Mobius.mobiusAxis h}

/-- Transport a genuine axis point by the actual Poincare action. -/
theorem mobiusGeodesicAxis_smul (f q : Mobius.complexMobiusGroup) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
    (hx : x ∈ mobiusGeodesicAxis f) : q • x ∈ mobiusGeodesicAxis (q * f * q⁻¹) := by
  obtain ⟨h, hh, hs, hx⟩ := hx
  refine ⟨q * h * q⁻¹, (Mobius.mobiusElliptic_conjugation h q).mpr hh,
    (Mobius.mobiusSameFixedPoints_conjugation h f q).mpr hs, ?_⟩
  rw [Mobius.mobiusAxis_conjugation]
  exact ⟨x, hx, rfl⟩

/-- The full actual geodesic axis transforms by the actual conjugacy action. -/
theorem mobiusGeodesicAxis_conjugation (f q : Mobius.complexMobiusGroup) :
    mobiusGeodesicAxis (q * f * q⁻¹) = (fun x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q • x) ''
      mobiusGeodesicAxis f := by
  ext y
  constructor
  · intro hy
    refine ⟨q⁻¹ • y, ?_, smul_inv_smul q y⟩
    have h := mobiusGeodesicAxis_smul (q * f * q⁻¹) q⁻¹ y hy
    have he : q⁻¹ * (q * f * q⁻¹) * (q⁻¹)⁻¹ = f := by group
    rwa [he] at h
  · rintro ⟨x, hx, rfl⟩
    exact mobiusGeodesicAxis_smul f q x hx

/-- Every nontranslation normal form has exactly the true standard vertical geodesic as axis. -/
theorem mobiusGeodesicAxis_standard (k : ℂˣ) (hk : (k : ℂ) ≠ 1) :
    mobiusGeodesicAxis (Mobius.mobiusStandardElement k) = mobiusVerticalGeodesic := by
  ext x
  constructor
  · rintro ⟨h, hh, hs, hx⟩
    have h0 : h.val (0 : ℂ) = (0 : ℂ) :=
      (hs _).mpr ((Mobius.mobiusStandardElement_boundary_fixed_iff k hk _).mpr (Or.inl rfl))
    have hi : h.val ∞ = ∞ :=
      (hs _).mpr ((Mobius.mobiusStandardElement_boundary_fixed_iff k hk _).mpr (Or.inr rfl))
    obtain ⟨m, hm, rfl⟩ := Mobius.mobius_fixed_zero_infty_standard h hh.1 h0 hi
    rw [Mobius.mobiusStandardElement_axis m hm ((Mobius.mobiusStandardElement_elliptic_iff m).mp hh).2] at hx
    exact hx
  · intro hx
    let m : ℂˣ := -1
    have hm : (m : ℂ) ≠ 1 := by norm_num [m]
    have hn : ‖(m : ℂ)‖ = 1 := by norm_num [m]
    refine ⟨Mobius.mobiusStandardElement m, Mobius.mobiusStandardElement_isElliptic m hm hn, ?_, ?_⟩
    · intro z
      rw [Mobius.mobiusStandardElement_boundary_fixed_iff m hm,
        Mobius.mobiusStandardElement_boundary_fixed_iff k hk]
    · rwa [Mobius.mobiusStandardElement_axis m hm hn]

/-- The eigenvalue model agrees with the nontranslation source normal form. -/
theorem eigenvalueMobius_standard (u : ℂ) (hu : u ≠ 0) (hunit : u ^ 2 ≠ 1) :
    eigenvalueMobius u hu = Mobius.mobiusStandardElement (Units.mk0 (u ^ 2) (pow_ne_zero 2 hu)) := by
  have hk : ((Units.mk0 (u ^ 2) (pow_ne_zero 2 hu) : ℂˣ) : ℂ) ≠ 1 := hunit
  rw [Mobius.mobiusStandardElement_affine, ite_eq_right hk]
  rfl

/-- The eigenvalue model has the true vertical geodesic as its complete axis. -/
theorem eigenvalueMobius_axis (u : ℂ) (hu : u ≠ 0) (hunit : u ^ 2 ≠ 1) :
    mobiusGeodesicAxis (eigenvalueMobius u hu) = mobiusVerticalGeodesic := by
  rw [eigenvalueMobius_standard u hu hunit]
  exact mobiusGeodesicAxis_standard _ hunit

/-- Distance to an actual complete axis is metric infimum distance in the original hyperbolic metric. -/
def mobiusGeodesicAxisDistance (f : Mobius.complexMobiusGroup) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
    : ℝ :=
  Metric.infDist x (mobiusGeodesicAxis f)

/-- The actual Poincare map is an isometry for the actual metric instance used here. -/
theorem mobius_geodesic_metric_isometry (q : Mobius.complexMobiusGroup) :
    Isometry (fun x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q • x) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [upperHalfSpaceHyperbolicMetricSpace_dist, upperHalfSpaceHyperbolicMetricSpace_dist,
    Mobius.upperHalfSpacePathDist_smul]

/-- Genuine distance to the axis is a conjugacy invariant at corresponding points. -/
theorem mobiusGeodesicAxisDistance_conjugation (f q : Mobius.complexMobiusGroup) (x :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    mobiusGeodesicAxisDistance (q * f * q⁻¹) (q • x) = mobiusGeodesicAxisDistance f x := by
  rw [mobiusGeodesicAxisDistance, mobiusGeodesicAxisDistance, mobiusGeodesicAxis_conjugation]
  exact Metric.infDist_image (mobius_geodesic_metric_isometry q)

/-- Translation length is the infimum of the genuine hyperbolic displacements. -/
def mobiusTranslationLength (f : Mobius.complexMobiusGroup) : ℝ :=
  sInf (Set.range (fun x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => Mobius.upperHalfSpacePathDist x (f • x)))

/-- Translation length is invariant under actual conjugation. -/
theorem mobiusTranslationLength_conjugation (f q : Mobius.complexMobiusGroup) :
    mobiusTranslationLength (q * f * q⁻¹) = mobiusTranslationLength f := by
  unfold mobiusTranslationLength
  congr 1
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨q⁻¹ • x, ?_⟩
    have h := Hyperbolic.QuaternionHalfSpace.parabolicDisplacement_conjugation f q (q⁻¹ • x)
    simpa only [smul_inv_smul] using h.symm
  · rintro ⟨x, rfl⟩
    exact ⟨q • x, Hyperbolic.QuaternionHalfSpace.parabolicDisplacement_conjugation f q x⟩

/-- Genuine distance between two points on the physical vertical geodesic. -/
theorem mobiusVerticalPoint_pathDist (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Mobius.upperHalfSpacePathDist (Mobius.mobiusVerticalPoint s hs) (Mobius.mobiusVerticalPoint t ht) =
      |Real.log (s / t)| := by
  unfold Mobius.upperHalfSpacePathDist
  rw [Mobius.mobiusVerticalPoint_hyperbolic, Mobius.mobiusVerticalPoint_hyperbolic,
    Hyperbolic.verticalPoint_pathDist]

/-- The genuine displacement on the standard axis is independent of height. -/
theorem eigenvalue_axis_displacement (u : ℂ) (hu : u ≠ 0) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
    (hx : x ∈ mobiusVerticalGeodesic) :
    Mobius.upperHalfSpacePathDist x (eigenvalueMobius u hu • x) = 2 * |Real.log ‖u‖| := by
  have ht : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val := x.property
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have he : x = Mobius.mobiusVerticalPoint (Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val) ht := by
    apply Subtype.ext
    have h := Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates x.val
    rw [show Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val = 0 from hx] at h
    exact h.symm
  have hF : eigenvalueMobius u hu • x =
      Mobius.mobiusVerticalPoint (‖u‖ ^ 2 * Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val) (by positivity) := by
    apply Subtype.ext
    rw [eigenvalueMobius_smul, show Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val = 0 from hx, mul_zero]
    rfl
  rw [hF]
  conv_lhs => arg 1; rw [he]
  rw [mobiusVerticalPoint_pathDist]
  have hdiv : Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val / (‖u‖ ^ 2 *
    Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val) = (‖u‖ ^ 2)⁻¹ := by
    field_simp
  rw [hdiv, Real.log_inv, Real.log_pow, abs_neg, abs_mul]
  norm_num

/-- All actual displacements dominate the displacement attained on the true axis. -/
theorem eigenvalue_translationLength_lower (u : ℂ) (hu : u ≠ 0) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    2 * |Real.log ‖u‖| ≤ Mobius.upperHalfSpacePathDist x (eigenvalueMobius u hu • x) := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have he := eigenvalue_displacement_identity u hu x
  have hv := eigenvalue_displacement_identity u hu (Mobius.mobiusVerticalPoint 1 zero_lt_one)
  have hd := eigenvalue_axis_displacement u hu (Mobius.mobiusVerticalPoint 1 zero_lt_one)
    (show _ ∈ mobiusVerticalGeodesic from Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint 0 1)
  rw [mobiusSinhDisplacement, hd] at hv
  simp only [Mobius.mobiusVerticalPoint, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint,
    norm_zero, zero_div,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero] at hv
  have hp : 0 ≤ (‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val‖ /
    Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val) ^ 2 * ‖u - u⁻¹‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS : Real.sinh |Real.log ‖u‖| ≤ mobiusSinhDisplacement (eigenvalueMobius u hu) x := by
    have hs : 0 ≤ Real.sinh |Real.log ‖u‖| := Real.sinh_nonneg_iff.mpr (abs_nonneg _)
    have ht := mobiusSinhDisplacement_nonneg (eigenvalueMobius u hu) x
    rw [show 2 * |Real.log ‖u‖| / 2 = |Real.log ‖u‖| by ring] at hv
    nlinarith
  rw [mobiusSinhDisplacement, Real.sinh_le_sinh] at hS
  linarith

/-- Translation length is attained on the true axis and has the genuine logarithmic value. -/
theorem eigenvalue_translationLength (u : ℂ) (hu : u ≠ 0) :
    mobiusTranslationLength (eigenvalueMobius u hu) = 2 * |Real.log ‖u‖| := by
  unfold mobiusTranslationLength
  have hb : BddBelow (Set.range (fun x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      Mobius.upperHalfSpacePathDist x (eigenvalueMobius u hu • x))) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact jorgensen_upperHalfSpacePathDist_nonneg _ _⟩
  apply le_antisymm
  · have h := csInf_le hb (Set.mem_range_self (Mobius.mobiusVerticalPoint 1 zero_lt_one))
    rwa [eigenvalue_axis_displacement u hu _ (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint 0 1)] at h
  · apply le_csInf ⟨_, Set.mem_range_self (Mobius.mobiusVerticalPoint 1 zero_lt_one)⟩
    rintro r ⟨x, rfl⟩
    exact eigenvalue_translationLength_lower u hu x

/-- The translation-length eigenvalue identity, in the genuine metric. -/
theorem eigenvalue_translationLength_identity (u : ℂ) (hu : u ≠ 0) :
    4 * Real.sinh (mobiusTranslationLength (eigenvalueMobius u hu) / 2) ^ 2 =
      (‖u‖ - ‖u‖⁻¹) ^ 2 := by
  rw [eigenvalue_translationLength, show 2 * |Real.log ‖u‖| / 2 = |Real.log ‖u‖| by ring,
    ← Real.abs_sinh, sq_abs, Real.sinh_log (norm_pos_iff.mpr hu)]
  ring

/-- The rotational term, derived invariantly from the genuine translation length and trace. -/
def mobiusRotationTerm (f : Mobius.complexMobiusGroup) : ℝ :=
  (‖Mobius.mobiusSquaredTrace f - 4‖ - 4 * Real.sinh (mobiusTranslationLength f / 2) ^ 2) / 4

/-- The invariantly expressed rotation term is a genuine conjugacy invariant. -/
theorem mobiusRotationTerm_conjugation (f q : Mobius.complexMobiusGroup) :
    mobiusRotationTerm (q * f * q⁻¹) = mobiusRotationTerm f := by
  rw [mobiusRotationTerm, mobiusRotationTerm, mobiusTranslationLength_conjugation,
    Mobius.mobiusSquaredTrace_conjugation]

/-- The true trace-square defect of the eigenvalue model is the eigenvalue-difference square. -/
theorem eigenvalue_trace_defect (u : ℂ) (hu : u ≠ 0) (hunit : u ^ 2 ≠ 1) :
    ‖Mobius.mobiusSquaredTrace (eigenvalueMobius u hu) - 4‖ = ‖u - u⁻¹‖ ^ 2 := by
  rw [eigenvalueMobius_standard u hu hunit, Mobius.mobiusSquaredTrace,
    Mobius.mobiusStandardElement_equiv, Mobius.Classification.standardElement_squaredTrace]
  change ‖u ^ 2 + (u ^ 2)⁻¹ + 2 - 4‖ = _
  have he : u ^ 2 + (u ^ 2)⁻¹ + 2 - 4 = (u - u⁻¹) ^ 2 := by field_simp; ring
  rw [he, norm_pow]

/-- The invariant rotation term is exactly the actual squared sine of the eigenvalue argument. -/
theorem eigenvalue_rotationTerm (u : ℂ) (hu : u ≠ 0) (hunit : u ^ 2 ≠ 1) :
    mobiusRotationTerm (eigenvalueMobius u hu) = mobiusEigenvalueRotation u := by
  rw [mobiusRotationTerm, eigenvalue_trace_defect u hu hunit,
    eigenvalue_translationLength_identity, eigenvalue_rotation_identity u hu]
  ring

/--
For the actual eigenvalue action, genuine translation length,
and actual infimum distance to the full geodesic axis.
-/
theorem eigenvalue_displacement_axis_identity (u : ℂ) (hu : u ≠ 0) (hunit : u ^ 2 ≠ 1)
    (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    mobiusSinhDisplacement (eigenvalueMobius u hu) x ^ 2 =
      Real.sinh (mobiusTranslationLength (eigenvalueMobius u hu) / 2) ^ 2 *
          Real.cosh (mobiusGeodesicAxisDistance (eigenvalueMobius u hu) x) ^ 2 +
        mobiusRotationTerm (eigenvalueMobius u hu) *
          Real.sinh (mobiusGeodesicAxisDistance (eigenvalueMobius u hu) x) ^ 2 := by
  have hd := eigenvalue_displacement_identity u hu x
  have ht := eigenvalue_translationLength_identity u hu
  have hr := eigenvalue_rotation_identity u hu
  have hc := Real.cosh_sq_sub_sinh_sq (Metric.infDist x mobiusVerticalGeodesic)
  rw [mobiusGeodesicAxisDistance, eigenvalueMobius_axis u hu hunit,
    eigenvalue_rotationTerm u hu hunit]
  rw [mobiusVerticalGeodesic_sinh_infDist] at hc ⊢
  nlinarith

/-- Every genuine nonidentity nonparabolic map admits the source eigenvalue normal form. -/
theorem mobius_nonparabolic_eigenvalue_normal_form (f : Mobius.complexMobiusGroup)
    (hf : f ≠ 1) (hp : ¬Mobius.MobiusParabolic f) :
    ∃ (u : ℂ) (hu : u ≠ 0), u ^ 2 ≠ 1 ∧
      ∃ q : Mobius.complexMobiusGroup, f = q * eigenvalueMobius u hu * q⁻¹ := by
  obtain ⟨k, hc⟩ := Mobius.mobius_nonidentity_conjugate_standard f hf
  have hk : (k : ℂ) ≠ 1 := by
    intro he
    have hu : k = 1 := Units.ext he
    apply hp
    apply (Mobius.mobiusBoundaryParabolic_iff_conjugate_translation f hf).mpr
    simpa only [hu] using hc
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (k : ℂ) (by norm_num : 0 < (2 : ℕ))
  have hun : u ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at hu; exact k.ne_zero hu.symm
  have hu1 : u ^ 2 ≠ 1 := by rwa [hu]
  have he : eigenvalueMobius u hun = Mobius.mobiusStandardElement k := by
    rw [eigenvalueMobius_standard u hun hu1]
    congr 1
    exact Units.ext hu
  obtain ⟨q, hq⟩ := isConj_iff.mp hc.symm
  exact ⟨u, hun, hu1, q, by rw [he]; exact hq.symm⟩

/-- The actual geometric axis depends only on the two genuine boundary fixed points. -/
theorem mobiusGeodesicAxis_eq_of_same_fixedPoints (f g : Mobius.complexMobiusGroup)
    (hfg : Mobius.MobiusSameFixedPoints f g) : mobiusGeodesicAxis f = mobiusGeodesicAxis g := by
  ext x
  constructor
  · rintro ⟨h, hh, hs, hx⟩
    exact ⟨h, hh, fun z => (hs z).trans (hfg z), hx⟩
  · rintro ⟨h, hh, hs, hx⟩
    exact ⟨h, hh, fun z => (hs z).trans (hfg z).symm, hx⟩

/-- For elliptic maps the complete geodesic axis is exactly the genuine interior fixed set. -/
theorem mobiusElliptic_geodesicAxis_eq_fixed_axis {f : Mobius.complexMobiusGroup} (hf : Mobius.MobiusElliptic f) :
    mobiusGeodesicAxis f = Mobius.mobiusAxis f := by
  obtain ⟨k, hk, hkn, hc⟩ := (Mobius.mobiusElliptic_iff_conjugate_standard f).mp hf
  obtain ⟨q, rfl⟩ := isConj_iff.mp hc.symm
  rw [mobiusGeodesicAxis_conjugation, Mobius.mobiusAxis_conjugation,
    mobiusGeodesicAxis_standard k hk, Mobius.mobiusStandardElement_axis k hk hkn]
  rfl

/-- Every nonparabolic axis is a complete unit-speed geodesic in the original length metric. -/
theorem mobiusGeodesicAxis_metric_param (f : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (hp : ¬Mobius.MobiusParabolic f) :
    ∃ γ : ℝ → Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, Set.range γ = mobiusGeodesicAxis f ∧
      ∀ s t, Mobius.upperHalfSpacePathDist (γ s) (γ t) = dist s t := by
  obtain ⟨u, hu, hu1, q, rfl⟩ := mobius_nonparabolic_eigenvalue_normal_form f hf hp
  refine ⟨fun s => q • Mobius.mobiusVerticalLogParam s, ?_, ?_⟩
  · rw [mobiusGeodesicAxis_conjugation, eigenvalueMobius_axis u hu hu1]
    change Set.range ((fun x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q • x) ∘
      Mobius.mobiusVerticalLogParam) = _
    rw [Set.range_comp, Mobius.mobiusVerticalLogParam_range]
    rfl
  · intro s t
    rw [Mobius.upperHalfSpacePathDist_smul, Mobius.mobiusVerticalLogParam_pathDist]

/-- Every such actual axis is literally a vertical line or a boundary-orthogonal Euclidean semicircle. -/
theorem mobiusGeodesicAxis_native_geodesic (f : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (hp : ¬Mobius.MobiusParabolic f) :
    Hyperbolic.IsHalfSpaceGeodesicLine 2
      (Mobius.upperHalfSpaceHyperbolicHomeomorph '' mobiusGeodesicAxis f) := by
  obtain ⟨γ, hγ, hd⟩ := mobiusGeodesicAxis_metric_param f hf hp
  have h := Hyperbolic.halfSpace_metric_geodesic_isLine (by norm_num : 1 ≤ 2)
    (fun t => Mobius.upperHalfSpaceHyperbolicHomeomorph (γ t)) (fun s t => hd s t)
  change Hyperbolic.IsHalfSpaceGeodesicLine 2
    (Set.range ((Mobius.upperHalfSpaceHyperbolicHomeomorph : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace →
      Hyperbolic.HyperbolicHalfSpace 2) ∘ γ)) at h
  rw [Set.range_comp, hγ] at h
  exact h

/-- Translation length is the constant attained displacement on the genuine complete axis. -/
theorem mobiusTranslationLength_axis_displacement (f : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (hp : ¬Mobius.MobiusParabolic f) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (hx : x ∈
      mobiusGeodesicAxis f) :
    Mobius.upperHalfSpacePathDist x (f • x) = mobiusTranslationLength f := by
  obtain ⟨u, hu, hu1, q, rfl⟩ := mobius_nonparabolic_eigenvalue_normal_form f hf hp
  rw [mobiusGeodesicAxis_conjugation, eigenvalueMobius_axis u hu hu1] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Hyperbolic.QuaternionHalfSpace.parabolicDisplacement_conjugation, mobiusTranslationLength_conjugation,
    eigenvalue_translationLength, eigenvalue_axis_displacement u hu y hy]

/-- The source displacement-to-axis identity holds for every genuine nonidentity nonparabolic map. -/
theorem mobius_displacement_axis_identity (f : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (hp : ¬Mobius.MobiusParabolic f) (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    mobiusSinhDisplacement f x ^ 2 =
      Real.sinh (mobiusTranslationLength f / 2) ^ 2 * Real.cosh (mobiusGeodesicAxisDistance f x) ^ 2 +
        mobiusRotationTerm f * Real.sinh (mobiusGeodesicAxisDistance f x) ^ 2 := by
  obtain ⟨u, hu, hu1, q, rfl⟩ := mobius_nonparabolic_eigenvalue_normal_form f hf hp
  have he : x = q • (q⁻¹ • x) := (smul_inv_smul q x).symm
  conv_lhs => rw [he]
  rw [mobiusSinhDisplacement_conjugation]
  conv_rhs => rw [he]
  rw [mobiusGeodesicAxisDistance_conjugation, mobiusTranslationLength_conjugation,
    mobiusRotationTerm_conjugation]
  exact eigenvalue_displacement_axis_identity u hu hu1 (q⁻¹ • x)

/-- Any genuine elliptic realization of the same two boundary endpoints gives precisely this axis. -/
theorem mobiusGeodesicAxis_eq_elliptic_axis (f h : Mobius.complexMobiusGroup)
    (hh : Mobius.MobiusElliptic h) (hs : Mobius.MobiusSameFixedPoints h f) :
    mobiusGeodesicAxis f = Mobius.mobiusAxis h :=
  (mobiusGeodesicAxis_eq_of_same_fixedPoints h f hs).symm.trans (mobiusElliptic_geodesicAxis_eq_fixed_axis hh)

/-- The complete geometric axis is nonempty, with a genuine same-endpoint elliptic realization. -/
theorem mobiusGeodesicAxis_exists_elliptic_realization (f : Mobius.complexMobiusGroup)
    (hf : f ≠ 1) (hp : ¬Mobius.MobiusParabolic f) :
    ∃ h : Mobius.complexMobiusGroup, Mobius.MobiusElliptic h ∧ Mobius.MobiusSameFixedPoints h f ∧
      mobiusGeodesicAxis f = Mobius.mobiusAxis h := by
  obtain ⟨γ, hγ, _⟩ := mobiusGeodesicAxis_metric_param f hf hp
  have hx : γ 0 ∈ mobiusGeodesicAxis f := hγ ▸ Set.mem_range_self 0
  obtain ⟨h, hh, hs, _⟩ := hx
  exact ⟨h, hh, hs, mobiusGeodesicAxis_eq_elliptic_axis f h hh hs⟩

/-- The genuine translation length is the least actual displacement, not only a lower bound. -/
theorem mobiusTranslationLength_isLeast (f : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (hp : ¬Mobius.MobiusParabolic f) :
    IsLeast (Set.range (fun x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => Mobius.upperHalfSpacePathDist x
      (f • x)))
      (mobiusTranslationLength f) := by
  constructor
  · obtain ⟨γ, hγ, _⟩ := mobiusGeodesicAxis_metric_param f hf hp
    exact ⟨γ 0, mobiusTranslationLength_axis_displacement f hf hp _ (hγ ▸ Set.mem_range_self 0)⟩
  · rintro r ⟨x, rfl⟩
    obtain ⟨u, hu, hu1, q, rfl⟩ := mobius_nonparabolic_eigenvalue_normal_form f hf hp
    rw [mobiusTranslationLength_conjugation, eigenvalue_translationLength]
    have h := eigenvalue_translationLength_lower u hu (q⁻¹ • x)
    have he := Hyperbolic.QuaternionHalfSpace.parabolicDisplacement_conjugation (eigenvalueMobius u hu) q (q⁻¹ • x)
    simpa only [smul_inv_smul] using h.trans_eq he.symm

/-- Elliptic maps have zero genuine translation length. -/
theorem mobiusElliptic_translationLength_eq_zero {f : Mobius.complexMobiusGroup} (hf : Mobius.MobiusElliptic f) :
    mobiusTranslationLength f = 0 := by
  obtain ⟨x, hx⟩ := hf.axis_nonempty
  have h := mobiusTranslationLength_axis_displacement f hf.1 hf.not_parabolic x
    ((mobiusElliptic_geodesicAxis_eq_fixed_axis hf).symm ▸ hx)
  have hfix : f • x = x := hx
  rw [hfix] at h
  have hz : Mobius.upperHalfSpacePathDist x x = 0 := by
    rw [← upperHalfSpaceHyperbolicMetricSpace_dist]
    exact dist_self x
  exact h.symm.trans hz

/-- The genuine squared-sine rotation invariant has its required geometric range. -/
theorem mobiusRotationTerm_mem_Icc (f : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (hp : ¬Mobius.MobiusParabolic f) : mobiusRotationTerm f ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨u, hu, hu1, q, rfl⟩ := mobius_nonparabolic_eigenvalue_normal_form f hf hp
  rw [mobiusRotationTerm_conjugation, eigenvalue_rotationTerm u hu hu1]
  exact ⟨sq_nonneg _, by simpa only [mobiusEigenvalueRotation] using Real.sin_sq_le_one (Complex.arg u)⟩

/-- Genuine hyperbolic maps have zero rotational sine term. -/
theorem mobiusHyperbolic_rotationTerm_eq_zero {f : Mobius.complexMobiusGroup} (hf : Mobius.MobiusHyperbolic f) :
    mobiusRotationTerm f = 0 := by
  obtain ⟨r, hr, ht⟩ := (Mobius.mobius_hyperbolic_iff_squaredTrace_real_gt_four f hf.1.1).mp hf
  obtain ⟨k, hki, hkp, hkn, hk⟩ := Mobius.exists_positive_standard_squaredTrace r hr
  have hc := (Mobius.mobius_isConj_iff_squaredTrace_eq f _ hf.1.1 (Mobius.mobiusStandardElement_ne_one k)).mpr
    (ht.trans hk.symm)
  let u : ℂ := (Real.sqrt (k : ℂ).re : ℝ)
  have hu2 : u ^ 2 = (k : ℂ) := by
    apply Complex.ext
    · simp only [u, ← Complex.ofReal_pow, Complex.ofReal_re]
      exact Real.sq_sqrt hkp.le
    · simpa only [u, ← Complex.ofReal_pow, Complex.ofReal_im] using hki.symm
  have hu : u ≠ 0 := by intro he; rw [he, zero_pow (by decide)] at hu2; exact k.ne_zero hu2.symm
  have hku : (k : ℂ) ≠ 1 := by intro he; exact hkn (by rw [he]; norm_num)
  have hu1 : u ^ 2 ≠ 1 := by rwa [hu2]
  have hmodel : eigenvalueMobius u hu = Mobius.mobiusStandardElement k := by
    rw [eigenvalueMobius_standard u hu hu1]
    congr 1
    exact Units.ext hu2
  obtain ⟨q, hq⟩ := isConj_iff.mp hc.symm
  rw [← hq, mobiusRotationTerm_conjugation, ← hmodel, eigenvalue_rotationTerm u hu hu1]
  simp [mobiusEigenvalueRotation, Complex.sin_arg, u]

end LowDimensionalTopology.Geometry.DiscreteGroups
