/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.SignatureHyperbolicBoundaryBlock
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicHalfTurns
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.NativeSegmentEndpoints
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The actual native shift translates true length coordinates on its axis. -/
theorem signatureBoundaryShift_axis (l u : ℝ) :
    signatureBoundaryShift l (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam u) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam (u + l) := by
  apply UpperHalfPlane.ext
  rw [signatureBoundaryShift_coe]
  apply Complex.ext
  · simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam]
  · simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, Real.exp_add]
    ring

theorem signatureBoundaryShift_zpow_axis (l u : ℝ) (n : ℤ) :
    (signatureBoundaryShift l ^ n) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam u) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam (u + (n : ℝ) * l) := by
  rw [signatureBoundaryShift_zpow, signatureBoundaryShift_axis]

/-- One literal finite geodesic cut between the perpendicular boundary rays. -/
def signatureBoundaryAxisCut (l : ℝ) : Set ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam 0) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam l)

theorem signatureBoundaryAxisCut_image (l : ℝ) (hl : 0 < l) :
    signatureBoundaryAxisCut l = _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam '' Icc 0 l :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment_eq_image_Icc _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_isHGeodesicParam hl

theorem signatureBoundaryAxis_param_range :
    range _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    rfl
  · intro hz
    refine ⟨Real.log z.im, ?_⟩
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hz.symm
    · exact Real.exp_log z.im_pos

/-- Every true closed cut is carried to the literal consecutive length interval. -/
theorem signatureBoundaryAxisCut_zpow_image (l : ℝ) (hl : 0 < l) (n : ℤ) :
    (signatureBoundaryShift l ^ n) '' signatureBoundaryAxisCut l =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam '' Icc ((n : ℝ) * l) (((n : ℝ) + 1) * l) := by
  rw [signatureBoundaryAxisCut_image l hl]
  ext z
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u + (n : ℝ) * l, ?_, (signatureBoundaryShift_zpow_axis l u n).symm⟩
    constructor <;> linarith only [hu.1, hu.2]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam (u - (n : ℝ) * l), ?_, ?_⟩
    · refine ⟨u - (n : ℝ) * l, ?_, rfl⟩
      constructor <;> linarith only [hu.1, hu.2]
    · rw [signatureBoundaryShift_zpow_axis]
      congr 1
      ring

/-- Original powers of the true hyperbolic boundary translation extend the
finite actual cut to its complete actual axis. No whole-group wall property is assumed. -/
theorem signatureBoundaryAxisCut_zpow_cover (l : ℝ) (hl : 0 < l) :
    (⋃ n : ℤ, (signatureBoundaryShift l ^ n) '' signatureBoundaryAxisCut l) =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  rw [← signatureBoundaryAxis_param_range]
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    rw [signatureBoundaryAxisCut_zpow_image l hl n] at hn
    obtain ⟨u, _hu, rfl⟩ := hn
    exact mem_range_self _
  · rintro ⟨u, rfl⟩
    let n : ℤ := ⌊u / l⌋
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    rw [signatureBoundaryAxisCut_zpow_image l hl n]
    refine ⟨u, ?_, rfl⟩
    constructor
    · exact (le_div_iff₀ hl).mp (Int.floor_le _)
    · exact ((div_lt_iff₀ hl).mp (Int.lt_floor_add_one _)).le

/-- A native normalization carries the actual finite physical cut to this same cut. -/
theorem signatureBoundaryAxisCut_normalize (q : ℍ ≃ᵢ ℍ) (a b : ℍ) (l : ℝ)
    (ha : q a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam 0)
    (hb : q b = _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam l) :
    q '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment a b = signatureBoundaryAxisCut l := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_image_closedHSegment, ha, hb]
  rfl

/-- The actual conjugated powers extend the original physical cut to its
complete physical axis. This supplies the geometric wall attached to a core cut. -/
theorem signatureBoundaryAxisCut_conjugate_cover (q : ℍ ≃ᵢ ℍ) (a b : ℍ)
    (l : ℝ) (hl : 0 < l) (ha : q a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam 0)
    (hb : q b = _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam l) :
    (⋃ n : ℤ, (q⁻¹ * (signatureBoundaryShift l ^ n) * q) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment a b) =
      (q⁻¹ : ℍ ≃ᵢ ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  calc
    _ = (q⁻¹ : ℍ ≃ᵢ ℍ) '' (⋃ n : ℤ, (signatureBoundaryShift l ^ n) '' signatureBoundaryAxisCut l) := by
      rw [image_iUnion]
      apply iUnion_congr
      intro n
      rw [← signatureBoundaryAxisCut_normalize q a b l ha hb, image_image, image_image]
      rfl
    _ = _ := by rw [signatureBoundaryAxisCut_zpow_cover l hl]

end LowDimensionalTopology.Geometry.Fuchsian
