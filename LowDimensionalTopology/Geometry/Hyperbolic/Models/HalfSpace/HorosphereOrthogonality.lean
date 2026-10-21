module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenAxes
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.HorosphereParametrization
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped OnePoint RealInnerProductSpace Quaternion ComplexConjugate Topology
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius

/-- Genuine Euclidean hyperbolic planes: vertical planes and zero-height-centred hemispheres. -/
inductive HorosphericalPlaneSpec where
  | vertical (a : ℂ) (d : ℝ) (ha : a ≠ 0)
  | hemisphere (c : ℂ) (r : ℝ) (hr : 0 < r)

/-- The actual physical carrier of a hyperbolic plane in H3. -/
def HorosphericalPlaneSpec.carrier (P : HorosphericalPlaneSpec) : Set UpperHalfSpace :=
  match P with
  | .vertical a d _ => {x | inner ℝ x.val (quaternionThreePoint a 0) = d}
  | .hemisphere c r _ => {x | ‖x.val - quaternionThreePoint c 0‖ = r}

/-- Incidence of an actual ideal point with the literal boundary circle or extended straight line. -/
def HorosphericalPlaneSpec.containsIdeal (P : HorosphericalPlaneSpec) (w : Mobius.ExtendedComplex) : Prop :=
  match P, w with
  | .vertical _ _ _, ∞ => True
  | .hemisphere _ _ _, ∞ => False
  | .vertical a d _, OnePoint.some w => inner ℝ (quaternionThreePoint w 0) (quaternionThreePoint a 0) = d
  | .hemisphere c r _, OnePoint.some w => ‖w - c‖ = r

/-- The true Euclidean normal to the tangent plane at a physical point. -/
def HorosphericalPlaneSpec.normal (P : HorosphericalPlaneSpec) (x : UpperHalfSpace) : quaternionThreeSpace :=
  match P with
  | .vertical a _ _ => quaternionThreePoint a 0
  | .hemisphere c _ _ => x.val - quaternionThreePoint c 0

/-- The actual Euclidean unit vertical vector. -/
def horosphereVerticalUnit : quaternionThreeSpace := quaternionThreePoint 0 1

/-- The normal to the genuine physical horosphere at infinity or its finite tangency point. -/
def horosphereNormal (w : Mobius.ExtendedComplex) (r : ℝ) (x : UpperHalfSpace) : quaternionThreeSpace :=
  match w with
  | ∞ => horosphereVerticalUnit
  | OnePoint.some w => x.val - quaternionThreePoint w r

/-- Actual Euclidean inner products in the fixed complex-height coordinates. -/
theorem horosphere_inner_coordinates (z w : ℂ) (t s : ℝ) :
    inner ℝ (quaternionThreePoint z t) (quaternionThreePoint w s) = (z * conj w).re + t * s := by
  change inner ℝ (quaternionThreePoint z t : ℍ) (quaternionThreePoint w s : ℍ) = _
  simp [Quaternion.inner_def, quaternionThreePoint, Complex.mul_re]

/-- A vertical plane has a genuine nonzero Euclidean normal. -/
theorem HorosphericalPlaneSpec.normal_ne_zero (P : HorosphericalPlaneSpec) (x : UpperHalfSpace) :
    P.normal x ≠ 0 := by
  cases P with
  | vertical a d ha =>
    intro he
    have hh := congrArg quaternionHorizontal he
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.normal,
      quaternionHorizontal_threePoint,
      quaternionHorizontal, Complex.zero_re, Complex.zero_im] using ha hh
  | hemisphere c r hr =>
    intro he
    have hh := congrArg quaternionHeight he
    have ht : 0 < quaternionHeight x.val := x.property
    change quaternionHeight x.val - 0 = 0 at hh
    linarith

/-- The finite physical horosphere is the literal sphere level within H3. -/
theorem frontier_horoballRegion_coe (w : ℂ) (r : ℝ) (hr : 0 < r) :
    frontier (horoballRegion (w : Mobius.ExtendedComplex) r) =
      {x : UpperHalfSpace | ‖x.val - quaternionThreePoint w r‖ = r} := by
  change frontier (Subtype.val ⁻¹' Metric.ball (quaternionThreePoint w r) r) = _
  rw [← isOpen_upperHalfSpaceSet.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
    continuous_subtype_val, frontier_ball _ hr.ne']
  ext x
  simp only [mem_preimage, Metric.mem_sphere, dist_eq_norm, mem_ofPred_eq]

/-- The physical horosphere at infinity is the actual positive horizontal plane level. -/
theorem frontier_horoballRegion_infty (r : ℝ) :
    frontier (horoballRegion ∞ r) = {x : UpperHalfSpace | quaternionHeight x.val = r} := by
  change frontier (Subtype.val ⁻¹' (quaternionHeightContinuous ⁻¹' Ioi r)) = _
  rw [← isOpen_upperHalfSpaceSet.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
    continuous_subtype_val, quaternionHeightContinuous.frontier_preimage quaternionHeight_surjective,
    frontier_Ioi]
  rfl

/-- The radius equality for a finite physical horosphere gives its literal normal sphere equation. -/
theorem horosphere_finite_norm_sq (w : ℂ) (r : ℝ) (hr : 0 < r) (x : UpperHalfSpace)
    (hx : x ∈ frontier (horoballRegion (w : Mobius.ExtendedComplex) r)) :
    ‖x.val - quaternionThreePoint w r‖ ^ 2 = r ^ 2 := by
  rw [frontier_horoballRegion_coe w r hr] at hx
  exact congrArg (fun s : ℝ => s ^ 2) hx

/-- Euclidean sphere tangents are orthogonal when the squared centre-distance is the sum of squared radii. -/
theorem horosphere_sphere_normals_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x h c : E) (r R : ℝ) (hh : ‖x - h‖ ^ 2 = r ^ 2) (hc : ‖x - c‖ ^ 2 = R ^ 2)
    (hch : ‖h - c‖ ^ 2 = r ^ 2 + R ^ 2) : inner ℝ (x - h) (x - c) = 0 := by
  have hs := norm_sub_sq_real (x - h) (x - c)
  have he : (x - h) - (x - c) = -(h - c) := by abel
  rw [he, norm_neg, hh, hc, hch] at hs
  linarith

/-- Every genuine vertical hyperbolic plane through the finite ideal base meets the physical horosphere orthogonally. -/
theorem horosphere_vertical_plane_orthogonal (w a : ℂ) (r d : ℝ) (_hr : 0 < r) (ha : a ≠ 0)
    (x : UpperHalfSpace) (_hx : x ∈ frontier (horoballRegion (w : Mobius.ExtendedComplex) r))
    (hP : x ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.vertical a d
      ha).carrier)
    (hw : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.vertical a d
      ha).containsIdeal (w : Mobius.ExtendedComplex)) :
    inner ℝ (horosphereNormal (w : Mobius.ExtendedComplex) r x)
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.vertical a d ha).normal x) = 0 := by
  change inner ℝ (x.val - quaternionThreePoint w r) (quaternionThreePoint a 0) = 0
  rw [inner_sub_left]
  have he : inner ℝ (quaternionThreePoint w r) (quaternionThreePoint a 0) =
      inner ℝ (quaternionThreePoint w 0) (quaternionThreePoint a 0) := by
    rw [horosphere_inner_coordinates, horosphere_inner_coordinates, mul_zero, mul_zero]
  rw [he, show inner ℝ x.val (quaternionThreePoint a 0) = d from hP,
    show inner ℝ (quaternionThreePoint w 0) (quaternionThreePoint a 0) = d from hw, sub_self]

/-- Every genuine hemispherical hyperbolic plane through the finite ideal base meets the physical horosphere orthogonally. -/
theorem horosphere_hemisphere_orthogonal (w c : ℂ) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (x : UpperHalfSpace) (hx : x ∈ frontier (horoballRegion (w : Mobius.ExtendedComplex) r))
    (hP : x ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.hemisphere c
      R hR).carrier)
    (hw : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.hemisphere c R
      hR).containsIdeal (w : Mobius.ExtendedComplex)) :
    inner ℝ (horosphereNormal (w : Mobius.ExtendedComplex) r x)
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.hemisphere c R hR).normal x) = 0 := by
  apply horosphere_sphere_normals_orthogonal x.val (quaternionThreePoint w r)
    (quaternionThreePoint c 0) r R (horosphere_finite_norm_sq w r hr x hx)
    (congrArg (fun s : ℝ => s ^ 2) hP)
  have h := horoball_distance_sq (upperHalfSpacePoint w r hr) c 0
  rw [upperHalfSpacePoint_horizontal, upperHalfSpacePoint_height, sub_zero, dist_eq_norm] at h
  have hw' : ‖w - c‖ = R := hw
  change ‖quaternionThreePoint w r - quaternionThreePoint c 0‖ ^ 2 = r ^ 2 + R ^ 2
  rw [hw'] at h
  change ‖quaternionThreePoint w r - quaternionThreePoint c 0‖ ^ 2 = R ^ 2 + r ^ 2 at h
  linarith

/-- All genuine hyperbolic planes through the ideal base meet a physical horosphere orthogonally. -/
theorem horosphere_all_planes_orthogonal (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r)
    (x : UpperHalfSpace) (hx : x ∈ frontier (horoballRegion w r))
    (P : HorosphericalPlaneSpec) (hP : x ∈ P.carrier) (hw : P.containsIdeal w) :
    inner ℝ (horosphereNormal w r x) (P.normal x) = 0 := by
  cases w using OnePoint.rec with
  | infty =>
    cases P with
    | vertical a d ha =>
      change inner ℝ (quaternionThreePoint 0 1) (quaternionThreePoint a 0) = 0
      rw [horosphere_inner_coordinates]
      simp
    | hemisphere c R hR => exact False.elim hw
  | coe w =>
    cases P with
    | vertical a d ha => exact horosphere_vertical_plane_orthogonal w a r d hr ha x hx hP hw
    | hemisphere c R hR => exact horosphere_hemisphere_orthogonal w c r R hr hR x hx hP hw

/-- The actual vertical Euclidean coordinate is inner product with the physical unit vertical vector. -/
theorem horosphere_inner_vertical (v : quaternionThreeSpace) :
    inner ℝ v horosphereVerticalUnit = quaternionHeight v := by
  rw [← quaternionThreePoint_coordinates v]
  rw [horosphereVerticalUnit, horosphere_inner_coordinates]
  simp

/-- Symmetric form of the actual vertical-coordinate identity. -/
theorem horosphere_vertical_inner (v : quaternionThreeSpace) :
    inner ℝ horosphereVerticalUnit v = quaternionHeight v := by
  rw [real_inner_comm, horosphere_inner_vertical]

/-- The actual vertical vector has Euclidean norm one. -/
theorem horosphereVerticalUnit_norm : ‖horosphereVerticalUnit‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← real_inner_self_eq_norm_sq, horosphere_inner_vertical]
  norm_num [horosphereVerticalUnit]

/-- Boundary-centred Euclidean distance never vanishes at a point of H3. -/
theorem horosphere_base_difference_ne_zero (w : ℂ) (x : UpperHalfSpace) :
    x.val - quaternionThreePoint w 0 ≠ 0 := by
  intro he
  have hh := congrArg quaternionHeight he
  have ht : 0 < quaternionHeight x.val := x.property
  change quaternionHeight x.val - 0 = 0 at hh
  linarith

/-- The actual normal field of all horospheres based at one ideal point. -/
def horosphereConormal (w : Mobius.ExtendedComplex) (x : UpperHalfSpace) : quaternionThreeSpace :=
  match w with
  | ∞ => horosphereVerticalUnit
  | OnePoint.some w => x.val - quaternionThreePoint w 0 -
      (‖x.val - quaternionThreePoint w 0‖ ^ 2 / (2 * quaternionHeight x.val)) • horosphereVerticalUnit

/-- A finite-base conormal has a nonzero pairing with the radius from its ideal base. -/
theorem horosphereConormal_inner_base (w : ℂ) (x : UpperHalfSpace) :
    inner ℝ (horosphereConormal (w : Mobius.ExtendedComplex) x) (x.val - quaternionThreePoint w 0) =
      ‖x.val - quaternionThreePoint w 0‖ ^ 2 / 2 := by
  have ht : 0 < quaternionHeight x.val := x.property
  change inner ℝ (x.val - quaternionThreePoint w 0 -
    (‖x.val - quaternionThreePoint w 0‖ ^ 2 / (2 * quaternionHeight x.val)) • horosphereVerticalUnit)
      (x.val - quaternionThreePoint w 0) = _
  rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_smul_left, horosphere_vertical_inner]
  change ‖x.val - quaternionThreePoint w 0‖ ^ 2 -
    ‖x.val - quaternionThreePoint w 0‖ ^ 2 / (2 * quaternionHeight x.val) *
      (quaternionHeight x.val - 0) = _
  field_simp
  ring

/-- The normal distribution is everywhere nondegenerate in actual H3. -/
theorem horosphereConormal_ne_zero (w : Mobius.ExtendedComplex) (x : UpperHalfSpace) :
    horosphereConormal w x ≠ 0 := by
  cases w using OnePoint.rec with
  | infty =>
    change horosphereVerticalUnit ≠ 0
    exact norm_ne_zero_iff.mp (by rw [horosphereVerticalUnit_norm]; norm_num)
  | coe w =>
    intro he
    have h := horosphereConormal_inner_base w x
    rw [he, inner_zero_left] at h
    have hp : 0 < ‖x.val - quaternionThreePoint w 0‖ :=
      norm_pos_iff.mpr (horosphere_base_difference_ne_zero w x)
    nlinarith

/-- A positive horospherical potential, expressed in the actual H3 coordinates. -/
def horospherePotential (w : Mobius.ExtendedComplex) (q : quaternionThreeSpace) : ℝ :=
  match w with
  | ∞ => quaternionHeight q
  | OnePoint.some w => quaternionHeight q / ‖q - quaternionThreePoint w 0‖ ^ 2

/-- The potential is strictly positive at every physical H3 point. -/
theorem horospherePotential_pos (w : Mobius.ExtendedComplex) (x : UpperHalfSpace) :
    0 < horospherePotential w x.val := by
  cases w using OnePoint.rec with
  | infty => exact x.property
  | coe w =>
    exact div_pos x.property (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
      (horosphere_base_difference_ne_zero w x)))

/-- The true physical finite sphere equation is equivalent to its positive potential level. -/
theorem horospherePotential_radius_level (w : ℂ) (r : ℝ) (hr : 0 < r) (x : UpperHalfSpace) :
    horospherePotential (w : Mobius.ExtendedComplex) x.val = 1 / (2 * r) ↔
      x ∈ frontier (horoballRegion (w : Mobius.ExtendedComplex) r) := by
  have hD : ‖x.val - quaternionThreePoint w 0‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (horosphere_base_difference_ne_zero w x))
  rw [frontier_horoballRegion_coe w r hr]
  change quaternionHeight x.val / ‖x.val - quaternionThreePoint w 0‖ ^ 2 = 1 / (2 * r) ↔
    ‖x.val - quaternionThreePoint w r‖ = r
  rw [← sq_eq_sq₀ (norm_nonneg _) hr.le, div_eq_div_iff hD (by positivity : 2 * r ≠ 0)]
  have h0 := horoball_distance_sq x w 0
  have h1 := horoball_distance_sq x w r
  rw [dist_eq_norm, sub_zero] at h0
  rw [dist_eq_norm] at h1
  constructor <;> intro h <;> nlinarith

/-- Every positive finite-base potential level is a full physical horosphere. -/
theorem horospherePotential_level_coe (w : ℂ) (k : ℝ) (hk : 0 < k) (x : UpperHalfSpace) :
    horospherePotential (w : Mobius.ExtendedComplex) x.val = k ↔
      x ∈ frontier (horoballRegion (w : Mobius.ExtendedComplex) (1 / (2 * k))) := by
  have h := horospherePotential_radius_level w (1 / (2 * k)) (by positivity) x
  have he : 1 / (2 * (1 / (2 * k))) = k := by field_simp
  rwa [he] at h

/-- The true physical horizontal sphere equation is equivalent to a positive potential level. -/
theorem horospherePotential_level_infty (k : ℝ) (x : UpperHalfSpace) :
    horospherePotential ∞ x.val = k ↔ x ∈ frontier (horoballRegion ∞ k) := by
  rw [frontier_horoballRegion_infty]
  rfl

/-- The actual Fréchet derivative of the Busemann-height potential annihilates exactly its conormal plane. -/
theorem horospherePotential_hasFDerivAt (w : Mobius.ExtendedComplex) (x : UpperHalfSpace) :
    ∃ c : ℝ, c ≠ 0 ∧ HasFDerivAt (horospherePotential w)
      (c • innerSL ℝ (horosphereConormal w x)) x.val := by
  cases w using OnePoint.rec with
  | infty =>
    refine ⟨1, one_ne_zero, ?_⟩
    have he : quaternionHeightContinuous = innerSL ℝ horosphereVerticalUnit := by
      ext v
      exact (horosphere_vertical_inner v).symm
    change HasFDerivAt (fun q => quaternionHeightContinuous q) (1 • innerSL ℝ horosphereVerticalUnit) x.val
    rw [one_smul, ← he]
    exact quaternionHeightContinuous.hasFDerivAt
  | coe w =>
    have ht : 0 < quaternionHeight x.val := x.property
    have hD : ‖x.val - quaternionThreePoint w 0‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (horosphere_base_difference_ne_zero w x))
    refine ⟨-2 * quaternionHeight x.val / (‖x.val - quaternionThreePoint w 0‖ ^ 2) ^ 2,
      div_ne_zero (mul_ne_zero (by norm_num) ht.ne') (pow_ne_zero 2 hD), ?_⟩
    have hN := ((hasFDerivAt_id x.val).sub_const (quaternionThreePoint w 0)).norm_sq
    have hI := (hasDerivAt_inv hD).comp_hasFDerivAt x.val hN
    have hd := (quaternionHeightContinuous.hasFDerivAt (x := x.val)).mul hI
    convert! hd using 1
    ext v
    simp only [horosphereConormal, innerSL_apply_apply, smul_apply,
      add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, quaternionHeightContinuous_apply,
      smul_eq_mul, inner_sub_left, real_inner_smul_left, horosphere_vertical_inner, id_eq, Function.comp_apply]
    field_simp [hD, ht.ne']
    ring

/-- A zero-height ambient vector is literally the complex-horizontal vector with its coordinates. -/
theorem horosphere_zero_height_coordinates (v : quaternionThreeSpace) (hv : quaternionHeight v = 0) :
    quaternionThreePoint (quaternionHorizontal v) 0 = v := by
  simpa only [hv] using quaternionThreePoint_coordinates v

/-- Literal boundary differences have precisely their ordinary complex Euclidean norm. -/
theorem horosphere_boundary_difference_norm (w c : ℂ) :
    ‖quaternionThreePoint w 0 - quaternionThreePoint c 0‖ = ‖w - c‖ := by
  have he : quaternionThreePoint w 0 - quaternionThreePoint c 0 = quaternionThreePoint (w - c) 0 := by
    apply Subtype.ext
    apply Quaternion.ext <;> simp [quaternionThreePoint]
  rw [he]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Mobius.quaternionThreePoint_norm_sq]
  norm_num

/-- The actual normals of all physical hyperbolic planes through the ideal point span its full conormal plane. -/
theorem horosphere_plane_normals_span_conormal_orthogonal (w : Mobius.ExtendedComplex) (x : UpperHalfSpace)
    (T : Submodule ℝ quaternionThreeSpace)
    (hT : ∀ P : HorosphericalPlaneSpec, x ∈ P.carrier → P.containsIdeal w → P.normal x ∈ T) :
    (Submodule.span ℝ {horosphereConormal w x})ᗮ ≤ T := by
  intro v hv
  by_cases hv0 : v = 0
  · simpa only [hv0] using T.zero_mem
  have hN : inner ℝ (horosphereConormal w x) v = 0 :=
    (Submodule.mem_orthogonal_singleton_iff_inner_right).mp hv
  have ht : 0 < quaternionHeight x.val := x.property
  cases w using OnePoint.rec with
  | infty =>
    have hh : quaternionHeight v = 0 := by
      simpa only [horosphereConormal, horosphere_vertical_inner] using hN
    have he := horosphere_zero_height_coordinates v hh
    have ha : quaternionHorizontal v ≠ 0 := by
      intro hz
      apply hv0
      rw [← he, hz]
      rfl
    let P := _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.vertical (quaternionHorizontal v)
      (inner ℝ x.val (quaternionThreePoint (quaternionHorizontal v) 0)) ha
    have hp := hT P rfl trivial
    change quaternionThreePoint (quaternionHorizontal v) 0 ∈ T at hp
    rwa [he] at hp
  | coe w =>
    change inner ℝ (x.val - quaternionThreePoint w 0 -
      (‖x.val - quaternionThreePoint w 0‖ ^ 2 / (2 * quaternionHeight x.val)) • horosphereVerticalUnit) v = 0 at hN
    rw [inner_sub_left, real_inner_smul_left, horosphere_vertical_inner] at hN
    have hmul : 2 * quaternionHeight x.val * inner ℝ (x.val - quaternionThreePoint w 0) v =
        ‖x.val - quaternionThreePoint w 0‖ ^ 2 * quaternionHeight v := by
      field_simp [ht.ne'] at hN
      linarith
    by_cases hs : quaternionHeight v = 0
    · have he := horosphere_zero_height_coordinates v hs
      have ha : quaternionHorizontal v ≠ 0 := by
        intro hz
        apply hv0
        rw [← he, hz]
        rfl
      let P := _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.vertical (quaternionHorizontal v)
        (inner ℝ x.val (quaternionThreePoint (quaternionHorizontal v) 0)) ha
      have hp : x ∈ P.carrier := rfl
      have hw : P.containsIdeal (w : Mobius.ExtendedComplex) := by
        change inner ℝ (quaternionThreePoint w 0) (quaternionThreePoint (quaternionHorizontal v) 0) =
          inner ℝ x.val (quaternionThreePoint (quaternionHorizontal v) 0)
        rw [he]
        have hd : inner ℝ (x.val - quaternionThreePoint w 0) v = 0 := by
          rw [hs] at hmul
          nlinarith
        rw [inner_sub_left] at hd
        linarith
      have hm := hT P hp hw
      change quaternionThreePoint (quaternionHorizontal v) 0 ∈ T at hm
      rwa [he] at hm
    · let c : quaternionThreeSpace := x.val - (quaternionHeight x.val / quaternionHeight v) • v
      have hc0 : quaternionHeight c = 0 := by
        change quaternionHeight x.val - (quaternionHeight x.val / quaternionHeight v) * quaternionHeight v = 0
        field_simp
        ring
      have hc := horosphere_zero_height_coordinates c hc0
      have hd : x.val - c = (quaternionHeight x.val / quaternionHeight v) • v := by
        dsimp [c]
        module
      have hcd : x.val - c ≠ 0 := by
        rw [hd]
        exact smul_ne_zero (div_ne_zero ht.ne' hs) hv0
      let R := ‖x.val - c‖
      have hR : 0 < R := norm_pos_iff.mpr hcd
      let P := _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.hemisphere (quaternionHorizontal c) R hR
      have hp : x ∈ P.carrier := by
        change ‖x.val - quaternionThreePoint (quaternionHorizontal c) 0‖ = R
        rw [hc]
      have hi : 2 * inner ℝ (x.val - c) (x.val - quaternionThreePoint w 0) =
          ‖x.val - quaternionThreePoint w 0‖ ^ 2 := by
        rw [hd, real_inner_smul_left, real_inner_comm]
        field_simp [hs]
        linarith
      have hbc : ‖quaternionThreePoint w 0 - c‖ ^ 2 = R ^ 2 := by
        have h := norm_sub_sq_real (x.val - c) (x.val - quaternionThreePoint w 0)
        have he : (x.val - c) - (x.val - quaternionThreePoint w 0) = quaternionThreePoint w 0 - c := by abel
        rw [he] at h
        change ‖quaternionThreePoint w 0 - c‖ ^ 2 = ‖x.val - c‖ ^ 2
        linear_combination h - hi
      have hw : P.containsIdeal (w : Mobius.ExtendedComplex) := by
        change ‖w - quaternionHorizontal c‖ = R
        rw [← horosphere_boundary_difference_norm, hc]
        exact (sq_eq_sq₀ (norm_nonneg _) hR.le).mp hbc
      have hm := hT P hp hw
      change x.val - quaternionThreePoint (quaternionHorizontal c) 0 ∈ T at hm
      rw [hc] at hm
      have hcanc : quaternionHeight v / quaternionHeight x.val *
          (quaternionHeight x.val / quaternionHeight v) = 1 := by field_simp
      have hf := T.smul_mem (quaternionHeight v / quaternionHeight x.val) hm
      rwa [hd, smul_smul, hcanc, one_smul] at hf

/-- The actual ambient quaternion subspace has real dimension three. -/
theorem horosphere_ambient_finrank : Module.finrank ℝ quaternionThreeSpace = 3 := by
  rw [← euclideanThreeQuaternion.toLinearEquiv.finrank_eq]
  exact finrank_euclideanSpace_fin

/-- The actual normal complement has exactly the dimension of a surface tangent plane. -/
theorem horosphere_conormal_orthogonal_finrank (w : Mobius.ExtendedComplex) (x : UpperHalfSpace) :
    Module.finrank ℝ (Submodule.span ℝ {horosphereConormal w x})ᗮ = 2 := by
  have h := (Submodule.span ℝ {horosphereConormal w x}).finrank_add_finrank_orthogonal
  rw [horosphere_ambient_finrank, finrank_span_singleton (horosphereConormal_ne_zero w x)] at h
  omega

/-- Normal orthogonality for a genuine two-dimensional parametrized tangent forces precisely the conormal tangent plane. -/
theorem horosphere_regular_tangent_eq (w : Mobius.ExtendedComplex) (x : UpperHalfSpace)
    (L : ℂ →L[ℝ] quaternionThreeSpace)
    (hL : ∀ P : HorosphericalPlaneSpec, x ∈ P.carrier → P.containsIdeal w →
      P.normal x ∈ LinearMap.range L.toLinearMap) :
    LinearMap.range L.toLinearMap = (Submodule.span ℝ {horosphereConormal w x})ᗮ := by
  apply (Submodule.eq_of_le_of_finrank_le (horosphere_plane_normals_span_conormal_orthogonal w x _ hL) ?_).symm
  rw [horosphere_conormal_orthogonal_finrank]
  simpa only [Complex.finrank_real_complex] using L.toLinearMap.finrank_range_le

/-- Orthogonality of actual tangent planes is equivalently orthogonality of every normal vector. -/
theorem horosphere_normal_mem_tangent_iff (T : Submodule ℝ quaternionThreeSpace) (N : quaternionThreeSpace) :
    N ∈ T ↔ ∀ n ∈ Tᗮ, inner ℝ n N = 0 := by
  rw [← Submodule.mem_orthogonal, Submodule.orthogonal_orthogonal]

/-- A genuine regular C1 surface chart in the ambient Euclidean topology. -/
structure HorosphereRegularChart (S : Set quaternionThreeSpace) where
  chart : OpenPartialHomeomorph S ℂ
  smooth : ContDiffOn ℝ 1 (fun z : ℂ => (chart.symm z).val) chart.target
  regular : ∀ z ∈ chart.target,
    Function.Injective (fderiv ℝ (fun z : ℂ => (chart.symm z).val) z)

/-- A regular C1 embedded surface is covered by actual rank-two homeomorphic surface charts. -/
def IsHorosphereRegularSurface (S : Set quaternionThreeSpace) : Prop :=
  ∀ x : S, ∃ e : HorosphereRegularChart S, x ∈ e.chart.source

/-- Actual regular surface tangent planes are orthogonal to every physical hyperbolic plane through the ideal base.
The condition is expressed by membership of the plane normal in the genuine derivative range. -/
def IsPlaneOrthogonalRegularSurface (w : Mobius.ExtendedComplex) (S : Set quaternionThreeSpace) : Prop :=
  IsHorosphereRegularSurface S ∧ ∃ hS : S ⊆ upperHalfSpaceSet,
    ∀ (e : HorosphereRegularChart S) (z : ℂ) (_hz : z ∈ e.chart.target),
      ∀ P : HorosphericalPlaneSpec,
        (⟨(e.chart.symm z).val, hS (e.chart.symm z).property⟩ : UpperHalfSpace) ∈ P.carrier →
        P.containsIdeal w → P.normal ⟨(e.chart.symm z).val,
          hS (e.chart.symm z).property⟩ ∈
            LinearMap.range (fderiv ℝ (fun a : ℂ => (e.chart.symm a).val) z).toLinearMap

/-- A genuine regular chart for an orthogonal surface has constant-potential tangent derivative. -/
theorem IsPlaneOrthogonalRegularSurface.chart_potential_fderiv_eq_zero
    {w : Mobius.ExtendedComplex} {S : Set quaternionThreeSpace} (h : IsPlaneOrthogonalRegularSurface w S)
    (e : HorosphereRegularChart S) (z : ℂ) (hz : z ∈ e.chart.target) :
    fderiv ℝ (fun a : ℂ => horospherePotential w (e.chart.symm a).val) z = 0 := by
  obtain ⟨_, hS, horth⟩ := h
  let x : UpperHalfSpace := ⟨(e.chart.symm z).val, hS (e.chart.symm z).property⟩
  let L := fderiv ℝ (fun a : ℂ => (e.chart.symm a).val) z
  have he : LinearMap.range L.toLinearMap = (Submodule.span ℝ {horosphereConormal w x})ᗮ :=
    horosphere_regular_tangent_eq w x L (horth e z hz)
  have hφ : DifferentiableAt ℝ (fun a : ℂ => (e.chart.symm a).val) z :=
    (e.smooth.differentiableOn one_ne_zero z hz).differentiableAt
      (e.chart.open_target.mem_nhds hz)
  obtain ⟨c, _, hc⟩ := horospherePotential_hasFDerivAt w x
  have hd := hc.comp z hφ.hasFDerivAt
  change fderiv ℝ (horospherePotential w ∘ fun a : ℂ => (e.chart.symm a).val) z = 0
  rw [hd.fderiv]
  ext v
  change c * inner ℝ (horosphereConormal w x) (L v) = 0
  have hv : L v ∈ (Submodule.span ℝ {horosphereConormal w x})ᗮ :=
    he ▸ LinearMap.mem_range_self L.toLinearMap v
  rw [(Submodule.mem_orthogonal_singleton_iff_inner_right).mp hv, mul_zero]

/-- The true Busemann potential is locally constant on every actual regular orthogonal surface. -/
theorem IsPlaneOrthogonalRegularSurface.potential_isLocallyConstant
    {w : Mobius.ExtendedComplex} {S : Set quaternionThreeSpace} (h : IsPlaneOrthogonalRegularSurface w S) :
    IsLocallyConstant (fun x : S => horospherePotential w x.val) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  obtain ⟨e, hx⟩ := h.1 x
  have hz : e.chart x ∈ e.chart.target := e.chart.map_source hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.chart.open_target (e.chart x) hz
  let F : ℂ → ℝ := fun a => horospherePotential w (e.chart.symm a).val
  have hdiff : DifferentiableOn ℝ F e.chart.target := by
    intro z hz
    obtain ⟨_, hS, _⟩ := h
    let q : UpperHalfSpace := ⟨(e.chart.symm z).val, hS (e.chart.symm z).property⟩
    obtain ⟨_, _, hq⟩ := horospherePotential_hasFDerivAt w q
    exact hq.differentiableAt.comp_differentiableWithinAt z (e.smooth.differentiableOn one_ne_zero z hz)
  have hconst (z : ℂ) (hz' : z ∈ Metric.ball (e.chart x) r) : F z = F (e.chart x) := by
    apply (convex_ball (e.chart x) r).is_const_of_fderivWithin_eq_zero (hdiff.mono hball) ?_
      hz' (Metric.mem_ball_self hr)
    intro a ha
    rw [fderivWithin_of_isOpen Metric.isOpen_ball ha]
    exact h.chart_potential_fderiv_eq_zero e a (hball ha)
  have hcont := e.chart.continuousAt hx
  have hs : ∀ᶠ y : S in 𝓝 x, y ∈ e.chart.source := e.chart.open_source.mem_nhds hx
  have hb : ∀ᶠ y : S in 𝓝 x, e.chart y ∈ Metric.ball (e.chart x) r :=
    hcont.eventually (Metric.ball_mem_nhds _ hr)
  have hev := hs.and hb
  filter_upwards [hev] with y hy
  have hc := hconst (e.chart y) hy.2
  change horospherePotential w (e.chart.symm (e.chart y)).val =
    horospherePotential w (e.chart.symm (e.chart x)).val at hc
  simpa only [e.chart.left_inv hy.1, e.chart.left_inv hx] using hc

/-- Every connected actual regular orthogonal surface lies in a single complete physical horosphere. -/
theorem IsPlaneOrthogonalRegularSurface.subset_physical_horosphere
    {w : Mobius.ExtendedComplex} {S : Set quaternionThreeSpace} (h : IsPlaneOrthogonalRegularSurface w S)
    (hc : IsPreconnected S) (hn : S.Nonempty) :
    ∃ r : ℝ, 0 < r ∧ S ⊆ Subtype.val '' frontier (horoballRegion w r) := by
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hc
  obtain ⟨x, hx⟩ := hn
  have hS : S ⊆ upperHalfSpaceSet := h.2.choose
  let X : UpperHalfSpace := ⟨x, hS hx⟩
  let k := horospherePotential w x
  have hk : 0 < k := horospherePotential_pos w X
  have hconst (y : S) : horospherePotential w y.val = k :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.IsPlaneOrthogonalRegularSurface.potential_isLocallyConstant h).apply_eq_of_preconnectedSpace y ⟨x, hx⟩
  cases w using OnePoint.rec with
  | infty =>
    refine ⟨k, hk, ?_⟩
    intro y hy
    refine ⟨⟨y, hS hy⟩, ?_, rfl⟩
    exact (horospherePotential_level_infty k _).mp (hconst ⟨y, hy⟩)
  | coe w =>
    refine ⟨1 / (2 * k), by positivity, ?_⟩
    intro y hy
    refine ⟨⟨y, hS hy⟩, ?_, rfl⟩
    exact (horospherePotential_level_coe w k hk _).mp (hconst ⟨y, hy⟩)

/-- On a true horosphere, its potential conormal is its literal Euclidean normal. -/
theorem horosphereConormal_eq_physical_normal (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r)
    (x : UpperHalfSpace) (hx : x ∈ frontier (horoballRegion w r)) :
    horosphereConormal w x = horosphereNormal w r x := by
  cases w using OnePoint.rec with
  | infty => rfl
  | coe w =>
    have ht : 0 < quaternionHeight x.val := x.property
    have h0 := horoball_distance_sq x w 0
    have h1 := horoball_distance_sq x w r
    rw [dist_eq_norm, sub_zero] at h0
    have hx' : ‖x.val - quaternionThreePoint w r‖ = r := by
      rwa [frontier_horoballRegion_coe w r hr] at hx
    rw [dist_eq_norm, hx'] at h1
    have hD : ‖x.val - quaternionThreePoint w 0‖ ^ 2 / (2 * quaternionHeight x.val) = r := by
      apply (div_eq_iff (by positivity : 2 * quaternionHeight x.val ≠ 0)).mpr
      nlinarith
    change x.val - quaternionThreePoint w 0 -
      (‖x.val - quaternionThreePoint w 0‖ ^ 2 / (2 * quaternionHeight x.val)) • horosphereVerticalUnit =
        x.val - quaternionThreePoint w r
    rw [hD]
    have he : quaternionThreePoint w r = quaternionThreePoint w 0 + r • horosphereVerticalUnit := by
      apply Subtype.ext
      apply Quaternion.ext <;> simp [quaternionThreePoint, horosphereVerticalUnit]
    rw [he]
    module

/-- Every actual plane normal through the ideal base belongs to the physical potential tangent plane. -/
theorem horosphereConormal_orthogonal_all_plane_normals (w : Mobius.ExtendedComplex) (x : UpperHalfSpace)
    (P : HorosphericalPlaneSpec) (hP : x ∈ P.carrier) (hw : P.containsIdeal w) :
    inner ℝ (horosphereConormal w x) (P.normal x) = 0 := by
  cases w using OnePoint.rec with
  | infty =>
    have ht : 0 < quaternionHeight x.val := x.property
    have hx : x ∈ frontier (horoballRegion ∞ (quaternionHeight x.val)) := by
      rw [frontier_horoballRegion_infty]
      rfl
    rw [horosphereConormal_eq_physical_normal ∞ _ ht x hx]
    exact horosphere_all_planes_orthogonal ∞ _ ht x hx P hP hw
  | coe w =>
    let k := horospherePotential (w : Mobius.ExtendedComplex) x.val
    have hk : 0 < k := horospherePotential_pos (w : Mobius.ExtendedComplex) x
    have hr : 0 < 1 / (2 * k) := by positivity
    have hx : x ∈ frontier (horoballRegion (w : Mobius.ExtendedComplex) (1 / (2 * k))) :=
      (horospherePotential_level_coe w k hk x).mp rfl
    rw [horosphereConormal_eq_physical_normal (w : Mobius.ExtendedComplex) _ hr x hx]
    exact horosphere_all_planes_orthogonal (w : Mobius.ExtendedComplex) _ hr x hx P hP hw

/-- Genuine regular rank-two parametrizations of a potential level have precisely the physical tangent plane. -/
theorem horosphere_level_regular_tangent_eq {w : Mobius.ExtendedComplex} {S : Set quaternionThreeSpace}
    (hS : S ⊆ upperHalfSpaceSet) (k : ℝ) (hlevel : ∀ x ∈ S, horospherePotential w x = k)
    (e : HorosphereRegularChart S) (z : ℂ) (hz : z ∈ e.chart.target) :
    LinearMap.range (fderiv ℝ (fun a : ℂ => (e.chart.symm a).val) z).toLinearMap =
      (Submodule.span ℝ {horosphereConormal w ⟨(e.chart.symm z).val, hS (e.chart.symm z).property⟩})ᗮ := by
  let x : UpperHalfSpace := ⟨(e.chart.symm z).val, hS (e.chart.symm z).property⟩
  let L := fderiv ℝ (fun a : ℂ => (e.chart.symm a).val) z
  have hφ : DifferentiableAt ℝ (fun a : ℂ => (e.chart.symm a).val) z :=
    (e.smooth.differentiableOn one_ne_zero z hz).differentiableAt (e.chart.open_target.mem_nhds hz)
  obtain ⟨c, hc, hpot⟩ := horospherePotential_hasFDerivAt w x
  have hcomp := (hpot.comp z hφ.hasFDerivAt).fderiv
  have hfun : (horospherePotential w ∘ fun a : ℂ => (e.chart.symm a).val) = fun _ => k :=
    funext fun a => hlevel _ (e.chart.symm a).property
  rw [hfun] at hcomp
  have hzero : fderiv ℝ (fun _ : ℂ => k) z = 0 := (hasFDerivAt_const k z).fderiv
  rw [hzero] at hcomp
  have hle : LinearMap.range L.toLinearMap ≤ (Submodule.span ℝ {horosphereConormal w x})ᗮ := by
    rintro v ⟨a, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    have h := congrArg (fun F : ℂ →L[ℝ] ℝ => F a) hcomp
    change 0 = c * inner ℝ (horosphereConormal w x) (L a) at h
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [horosphere_conormal_orthogonal_finrank]
  simpa only [Complex.finrank_real_complex] using
    L.toLinearMap.finrank_range_of_inj (e.regular z hz)

/-- An actual regular C1 level surface is orthogonal to all actual hyperbolic planes through its ideal base. -/
theorem horosphere_potential_level_isPlaneOrthogonal {w : Mobius.ExtendedComplex} {S : Set quaternionThreeSpace}
    (hregular : IsHorosphereRegularSurface S) (hS : S ⊆ upperHalfSpaceSet)
    (k : ℝ) (hlevel : ∀ x ∈ S, horospherePotential w x = k) :
    IsPlaneOrthogonalRegularSurface w S := by
  refine ⟨hregular, hS, ?_⟩
  intro e z hz P hP hw
  rw [horosphere_level_regular_tangent_eq hS k hlevel e z hz]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    (horosphereConormal_orthogonal_all_plane_normals w _ P hP hw)

/-- The positive scalar value of the actual potential on a physical radius-r horosphere. -/
def horosphereLevelValue (w : Mobius.ExtendedComplex) (r : ℝ) : ℝ :=
  match w with
  | ∞ => r
  | OnePoint.some _ => 1 / (2 * r)

/-- The true physical frontier in the ambient Euclidean space is exactly its positive potential level in H3. -/
theorem horosphere_frontier_image_eq_potential_level (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) :
    Subtype.val '' frontier (horoballRegion w r) =
      {q : quaternionThreeSpace | q ∈ upperHalfSpaceSet ∧ horospherePotential w q = horosphereLevelValue w r} := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    cases w using OnePoint.rec with
    | infty => exact (horospherePotential_level_infty r x).mpr hx
    | coe w => exact (horospherePotential_radius_level w r hr x).mpr hx
  · rintro ⟨hq, hv⟩
    refine ⟨⟨q, hq⟩, ?_, rfl⟩
    cases w using OnePoint.rec with
    | infty => exact (horospherePotential_level_infty r _).mp hv
    | coe w => exact (horospherePotential_radius_level w r hr _).mp hv

/-- The actual regular orthogonal connected-surface bridge yields equality of the actual potential at any two points. -/
theorem IsPlaneOrthogonalRegularSurface.potential_eq_of_mem
    {w : Mobius.ExtendedComplex} {S : Set quaternionThreeSpace} (h : IsPlaneOrthogonalRegularSurface w S)
    (hc : IsPreconnected S) {x y : quaternionThreeSpace} (hx : x ∈ S) (hy : y ∈ S) :
    horospherePotential w x = horospherePotential w y := by
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hc
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.IsPlaneOrthogonalRegularSurface.potential_isLocallyConstant h).apply_eq_of_preconnectedSpace
    ⟨x, hx⟩ ⟨y, hy⟩

/-- The completeness implicit in the source surface characterization is explicit maximality among
actual connected regular C1 surfaces with the genuine tangent-normal orthogonality property. -/
def IsMaximalConnectedPlaneOrthogonalSurface (w : Mobius.ExtendedComplex) (S : Set quaternionThreeSpace) : Prop :=
  IsPlaneOrthogonalRegularSurface w S ∧ IsConnected S ∧
    ∀ T : Set quaternionThreeSpace, IsPlaneOrthogonalRegularSurface w T → IsConnected T → S ⊆ T → T ⊆ S

/-- A full physical horosphere with its actual regular atlas is maximal among the actual orthogonal connected surfaces. -/
theorem horosphere_physical_frontier_isMaximal_of_regular (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r)
    (hregular : IsHorosphereRegularSurface (Subtype.val '' frontier (horoballRegion w r)))
    (hconnected : IsConnected (Subtype.val '' frontier (horoballRegion w r))) :
    IsMaximalConnectedPlaneOrthogonalSurface w (Subtype.val '' frontier (horoballRegion w r)) := by
  let S : Set quaternionThreeSpace := Subtype.val '' frontier (horoballRegion w r)
  have hS : S ⊆ upperHalfSpaceSet := by rintro q ⟨x, hx, rfl⟩; exact x.property
  have hlevel : ∀ x ∈ S, horospherePotential w x = horosphereLevelValue w r := by
    intro x hx
    exact ((horosphere_frontier_image_eq_potential_level w r hr ▸ hx) :
      x ∈ {q | q ∈ upperHalfSpaceSet ∧ horospherePotential w q = horosphereLevelValue w r}).2
  have horth := horosphere_potential_level_isPlaneOrthogonal hregular hS _ hlevel
  refine ⟨horth, hconnected, ?_⟩
  intro T hT hcT hsub y hy
  obtain ⟨x, hx⟩ := hconnected.nonempty
  have hxy := _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.IsPlaneOrthogonalRegularSurface.potential_eq_of_mem hT hcT.isPreconnected hy (hsub hx)
  obtain ⟨hTH, _⟩ := hT.2
  rw [horosphere_frontier_image_eq_potential_level w r hr]
  exact ⟨hTH hy, hxy.trans (hlevel x hx)⟩

/-- No extra global graph condition is needed for the converse: actual regular connected orthogonal
surfaces are contained in a physical horosphere, and maximality makes that containment equality. -/
theorem maximal_orthogonal_surface_eq_physical_frontier
    (w : Mobius.ExtendedComplex) (S : Set quaternionThreeSpace)
    (h : IsMaximalConnectedPlaneOrthogonalSurface w S)
    (hfull : ∀ r : ℝ, 0 < r → IsPlaneOrthogonalRegularSurface w
      (Subtype.val '' frontier (horoballRegion w r)) ∧
        IsConnected (Subtype.val '' frontier (horoballRegion w r))) :
    ∃ r : ℝ, 0 < r ∧ S = Subtype.val '' frontier (horoballRegion w r) := by
  obtain ⟨r, hr, hsub⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.IsPlaneOrthogonalRegularSurface.subset_physical_horosphere h.1
    h.2.1.isPreconnected h.2.1.nonempty
  obtain ⟨horth, hconn⟩ := hfull r hr
  exact ⟨r, hr, subset_antisymm hsub (h.2.2 _ horth hconn hsub)⟩

/-- Literal ambient defining equations for the physical hyperbolic planes. -/
def HorosphericalPlaneSpec.definingFunction (P : HorosphericalPlaneSpec) (q : quaternionThreeSpace) : ℝ :=
  match P with
  | .vertical a d _ => inner ℝ q (quaternionThreePoint a 0) - d
  | .hemisphere c r _ => ‖q - quaternionThreePoint c 0‖ ^ 2 - r ^ 2

/-- The literal physical carrier is exactly the zero level of its actual smooth equation. -/
theorem HorosphericalPlaneSpec.carrier_iff_definingFunction (P : HorosphericalPlaneSpec) (x : UpperHalfSpace) :
    x ∈ P.carrier ↔ P.definingFunction x.val = 0 := by
  cases P with
  | vertical a d ha => exact (sub_eq_zero).symm
  | hemisphere c r hr =>
    change ‖x.val - quaternionThreePoint c 0‖ = r ↔ ‖x.val - quaternionThreePoint c 0‖ ^ 2 - r ^ 2 = 0
    rw [sub_eq_zero, sq_eq_sq₀ (norm_nonneg _) hr.le]

/-- The specified plane normals are the actual differentials of the actual smooth defining equations. -/
theorem HorosphericalPlaneSpec.definingFunction_hasFDerivAt (P : HorosphericalPlaneSpec) (x : UpperHalfSpace) :
    ∃ c : ℝ, 0 < c ∧ HasFDerivAt P.definingFunction (c • innerSL ℝ (P.normal x)) x.val := by
  cases P with
  | vertical a d ha =>
    refine ⟨1, zero_lt_one, ?_⟩
    have h := ((innerSL ℝ (quaternionThreePoint a 0)).hasFDerivAt (x := x.val)).sub_const d
    convert! h using 1
    · funext q
      exact congrArg (fun t : ℝ => t - d) (real_inner_comm _ _)
    · simp only [one_smul,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.normal]
  | hemisphere c r hr =>
    refine ⟨2, by norm_num, ?_⟩
    have h := (((hasFDerivAt_id x.val).sub_const (quaternionThreePoint c 0)).norm_sq).sub_const (r ^ 2)
    convert! h using 1
    ext v
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.normal, two_smul]

/-- The actual tangent plane is the kernel of the genuine defining differential. -/
def HorosphericalPlaneSpec.tangent (P : HorosphericalPlaneSpec) (x :
  UpperHalfSpace) : Submodule ℝ quaternionThreeSpace :=
  LinearMap.ker (fderiv ℝ P.definingFunction x.val).toLinearMap

/-- The actual differential-kernel tangent plane is exactly the orthogonal complement of the actual nonzero normal. -/
theorem HorosphericalPlaneSpec.tangent_eq_normal_orthogonal (P : HorosphericalPlaneSpec) (x : UpperHalfSpace) :
    P.tangent x = (Submodule.span ℝ {P.normal x})ᗮ := by
  obtain ⟨c, hc, hd⟩ := P.definingFunction_hasFDerivAt x
  ext v
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.HorosphericalPlaneSpec.tangent, hd.fderiv,
    LinearMap.mem_ker,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  change c * inner ℝ (P.normal x) v = 0 ↔ inner ℝ (P.normal x) v = 0
  exact mul_eq_zero.trans (or_iff_right hc.ne')

/-- The chart derivative-range condition is precisely orthogonality of the actual surface and plane normal spaces. -/
theorem horosphere_actual_tangent_orthogonality_iff (T : Submodule ℝ quaternionThreeSpace)
    (P : HorosphericalPlaneSpec) (x : UpperHalfSpace) :
    P.normal x ∈ T ↔ ∀ n ∈ Tᗮ, ∀ m ∈ (P.tangent x)ᗮ, inner ℝ n m = 0 := by
  rw [P.tangent_eq_normal_orthogonal, Submodule.orthogonal_orthogonal]
  constructor
  · intro hN n hn m hm
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
    rw [real_inner_smul_right, (Submodule.mem_orthogonal' T n).mp hn _ hN, mul_zero]
  · intro h
    apply (horosphere_normal_mem_tangent_iff T (P.normal x)).mpr
    intro n hn
    exact h n hn _ (Submodule.mem_span_singleton_self _)

/-- The global physical C1 parametrization is exactly the topological boundary of the actual horoball inside H3. -/
theorem horospherePhysicalSurface_eq_frontier_image (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) :
    horospherePhysicalSurface w r = Subtype.val '' frontier (horoballRegion w r) := by
  ext q
  constructor
  · rintro ⟨hq, hv⟩
    refine ⟨⟨q, hq⟩, ?_, rfl⟩
    cases w using OnePoint.rec with
    | infty =>
      rw [frontier_horoballRegion_infty]
      exact hv
    | coe w =>
      rw [frontier_horoballRegion_coe w r hr]
      exact hv
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    cases w using OnePoint.rec with
    | infty => rwa [frontier_horoballRegion_infty] at hx
    | coe w => rwa [frontier_horoballRegion_coe w r hr] at hx

/-- The real global physical parametrization supplies an actual rank-two C1 surface chart. -/
def horospherePhysicalRegularChart (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) :
    HorosphereRegularChart (horospherePhysicalSurface w r) where
  chart := (horosphereParamHomeomorph w r hr).symm.toOpenPartialHomeomorph
  smooth := (horosphereParamHomeomorph_contDiff w r hr).contDiffOn
  regular := fun z _ => horosphereParamHomeomorph_fderiv_injective w r hr z

/-- Every point of a full physical horosphere belongs to a genuine regular C1 surface chart. -/
theorem horospherePhysicalSurface_regular (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) :
    IsHorosphereRegularSurface (horospherePhysicalSurface w r) := by
  intro x
  exact ⟨horospherePhysicalRegularChart w r hr, Set.mem_univ x⟩

/-- The full physical horosphere, including both the finite-sphere and horizontal-plane cases, is connected. -/
theorem horospherePhysicalSurface_isConnected (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) :
    IsConnected (horospherePhysicalSurface w r) := by
  let H := horosphereParamHomeomorph w r hr
  have hc : Continuous (fun z : ℂ => (H z).val) := continuous_subtype_val.comp H.continuous
  have he : (fun z : ℂ => (H z).val) '' Set.univ = horospherePhysicalSurface w r := by
    ext q
    constructor
    · rintro ⟨z, _, rfl⟩
      exact (H z).property
    · intro hq
      obtain ⟨z, hz⟩ := H.surjective ⟨q, hq⟩
      exact ⟨z, Set.mem_univ z, congrArg Subtype.val hz⟩
  have h := isConnected_univ.image (fun z : ℂ => (H z).val) hc.continuousOn
  rwa [he] at h

/-- Every true physical frontier has an actual regular C1 atlas and is connected. -/
theorem horosphere_physical_frontier_regular_connected (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) :
    IsHorosphereRegularSurface (Subtype.val '' frontier (horoballRegion w r)) ∧
      IsConnected (Subtype.val '' frontier (horoballRegion w r)) := by
  rw [← horospherePhysicalSurface_eq_frontier_image w r hr]
  exact ⟨horospherePhysicalSurface_regular w r hr, horospherePhysicalSurface_isConnected w r hr⟩

/-- The full physical horosphere has the actual regular tangent-plane orthogonality property. -/
theorem horosphere_physical_frontier_isPlaneOrthogonal (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) :
    IsPlaneOrthogonalRegularSurface w (Subtype.val '' frontier (horoballRegion w r)) := by
  have hreg := (horosphere_physical_frontier_regular_connected w r hr).1
  have hH : Subtype.val '' frontier (horoballRegion w r) ⊆ upperHalfSpaceSet := by
    rintro q ⟨x, hx, rfl⟩
    exact x.property
  apply horosphere_potential_level_isPlaneOrthogonal hreg hH (horosphereLevelValue w r)
  intro x hx
  rw [horosphere_frontier_image_eq_potential_level w r hr] at hx
  exact hx.2

/-- A genuine full horosphere is a maximal connected regular C1 surface orthogonal to the full family of actual hyperbolic planes through its base. -/
theorem horosphere_physical_frontier_isMaximal (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r) :
    IsMaximalConnectedPlaneOrthogonalSurface w (Subtype.val '' frontier (horoballRegion w r)) := by
  obtain ⟨hreg, hconn⟩ := horosphere_physical_frontier_regular_connected w r hr
  exact horosphere_physical_frontier_isMaximal_of_regular w r hr hreg hconn

/--
The intrinsic orthogonality characterization, with the necessary completeness
condition stated as maximality among actual connected regular C1 surfaces.
-/
theorem horosphere_orthogonality_characterization (w : Mobius.ExtendedComplex) (S : Set quaternionThreeSpace) :
    IsMaximalConnectedPlaneOrthogonalSurface w S ↔
      ∃ r : ℝ, 0 < r ∧ S = Subtype.val '' frontier (horoballRegion w r) := by
  constructor
  · intro h
    apply maximal_orthogonal_surface_eq_physical_frontier w S h
    intro r hr
    exact ⟨horosphere_physical_frontier_isPlaneOrthogonal w r hr,
      (horosphere_physical_frontier_regular_connected w r hr).2⟩
  · rintro ⟨r, hr, rfl⟩
    exact horosphere_physical_frontier_isMaximal w r hr

/-- The source's original physical horosphere definition agrees with the actual regular intrinsic characterization. -/
theorem isHorosphere_iff_maximal_connected_orthogonal (A : Set UpperHalfSpace) :
    IsHorosphere A ↔ ∃ w : Mobius.ExtendedComplex,
      IsMaximalConnectedPlaneOrthogonalSurface w (Subtype.val '' A) := by
  constructor
  · rintro ⟨D, ⟨w, r, hr, rfl⟩, rfl⟩
    exact ⟨w, horosphere_physical_frontier_isMaximal w r hr⟩
  · rintro ⟨w, hw⟩
    obtain ⟨r, hr, he⟩ := (horosphere_orthogonality_characterization w _).mp hw
    have hA : A = frontier (horoballRegion w r) :=
      Set.image_injective.mpr Subtype.val_injective he
    refine ⟨horoballRegion w r, ⟨w, r, hr, rfl⟩, hA⟩

/-- The tangent inner product belonging to the original reciprocal-height density,
transported through the genuine Euclidean quaternion coordinate isometry. -/
def horosphereHyperbolicTangentInner (x : UpperHalfSpace) (v u : quaternionThreeSpace) : ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfSpaceDensity 2 (Mobius.upperHalfSpaceHyperbolicHomeomorph
    x) ^ 2 *
    inner ℝ (euclideanThreeQuaternion.symm v) (euclideanThreeQuaternion.symm u)

/-- The actual hyperbolic tangent inner product is the Euclidean one times the positive squared native density. -/
theorem horosphereHyperbolicTangentInner_eq (x : UpperHalfSpace) (v u : quaternionThreeSpace) :
    horosphereHyperbolicTangentInner x v u = (1 / quaternionHeight x.val) ^ 2 * inner ℝ v u := by
  rw [horosphereHyperbolicTangentInner, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfSpaceDensity_apply,
    Mobius.upperHalfSpaceHyperbolicHomeomorph_val, Mobius.euclideanThreeQuaternion_symm_height,
    euclideanThreeQuaternion.symm.inner_map_map]

/-- Actual hyperbolic orthogonality is exactly actual Euclidean orthogonality in this conformal metric. -/
theorem horosphere_hyperbolic_orthogonality_iff (x : UpperHalfSpace) (v u : quaternionThreeSpace) :
    horosphereHyperbolicTangentInner x v u = 0 ↔ inner ℝ v u = 0 := by
  rw [horosphereHyperbolicTangentInner_eq, mul_eq_zero]
  have ht : 0 < quaternionHeight x.val := x.property
  exact or_iff_right (pow_ne_zero 2 (one_div_ne_zero ht.ne'))

/-- The physical orthogonality statement also holds in the native density tangent metric. -/
theorem horosphere_all_planes_hyperbolic_orthogonal (w : Mobius.ExtendedComplex) (r : ℝ) (hr : 0 < r)
    (x : UpperHalfSpace) (hx : x ∈ frontier (horoballRegion w r))
    (P : HorosphericalPlaneSpec) (hP : x ∈ P.carrier) (hw : P.containsIdeal w) :
    horosphereHyperbolicTangentInner x (horosphereNormal w r x) (P.normal x) = 0 :=
  (horosphere_hyperbolic_orthogonality_iff x _ _).mpr
    (horosphere_all_planes_orthogonal w r hr x hx P hP hw)

/-- The actual regular tangent characterization is equivalent with the native hyperbolic tangent inner product. -/
theorem horosphere_actual_hyperbolic_tangent_orthogonality_iff (T : Submodule ℝ quaternionThreeSpace)
    (P : HorosphericalPlaneSpec) (x : UpperHalfSpace) :
    P.normal x ∈ T ↔ ∀ n ∈ Tᗮ, ∀ m ∈ (P.tangent x)ᗮ, horosphereHyperbolicTangentInner x n m = 0 := by
  simp_rw [horosphere_hyperbolic_orthogonality_iff]
  exact horosphere_actual_tangent_orthogonality_iff T P x

end LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
