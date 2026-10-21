module
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteRotationSectors
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ModelCoordinates

/-! Actual linear half-plane and geodesic convexity descriptions of finite rotation sectors. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The genuine imaginary coordinate of a positive-radius angular point. -/
theorem rotationSector_radial_im (r t : ℝ) :
    ((r : ℂ) * (Circle.exp t : ℂ)).im = r * Real.sin t := by
  simp [Circle.coe_exp,Complex.exp_mul_I,←Complex.ofReal_sin]

/-- Multiplication by a genuine rotation subtracts its angle on an actual radial point. -/
theorem rotationSector_rotated_radial_im (r s t : ℝ) :
    ((Circle.exp s : ℂ) * ((r : ℂ) * (Circle.exp t : ℂ))).im = r * Real.sin (s+t) := by
  have he : (Circle.exp (s+t) : ℂ) = (Circle.exp s : ℂ) * (Circle.exp t : ℂ) := by
    exact congrArg (fun u : Circle => (u : ℂ)) (Circle.exp_add s t)
  rw [show (Circle.exp s : ℂ) * ((r : ℂ) * (Circle.exp t : ℂ)) =
    (r : ℂ) * ((Circle.exp s : ℂ) * (Circle.exp t : ℂ)) by ring,←he]
  exact rotationSector_radial_im r (s+t)

/-- A genuine angular sector of width at most pi is exactly two strict linear half-planes. -/
theorem rotationSector_halfPlanes_iff (P : ℝ) (hP : 0<P) (hPpi : P≤Real.pi) (z : ℂ) :
    (∃ r : ℝ,0<r ∧ ∃t∈Ioo (0 : ℝ) P,z=(r : ℂ)*(Circle.exp t : ℂ)) ↔
      0<z.im ∧ ((Circle.exp (-P) : ℂ)*z).im<0 := by
  constructor
  · rintro ⟨r,hr,t,ht,rfl⟩
    rw [rotationSector_radial_im,rotationSector_rotated_radial_im]
    refine ⟨mul_pos hr (Real.sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans_le hPpi)),?_⟩
    exact mul_neg_of_pos_of_neg hr (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [ht.2]) (by linarith [ht.1]))
  · rintro ⟨him,hrot⟩
    have hz : z≠0 := by intro he;rw [he] at him;exact lt_irrefl _ him
    have hr : 0<‖z‖ := norm_pos_iff.mpr hz
    have hrep : z=(‖z‖ : ℂ)*(Circle.exp (Complex.arg z) : ℂ) :=
      (Complex.norm_mul_exp_arg_mul_I z).symm
    have he : z.im=‖z‖*Real.sin (Complex.arg z) :=
      (congrArg Complex.im hrep).trans (rotationSector_radial_im ‖z‖ (Complex.arg z))
    have ha : 0<Complex.arg z := by
      have hn : 0≤Complex.arg z := Complex.arg_nonneg_iff.mpr him.le
      by_contra hnot
      have hzarg : Complex.arg z=0 := le_antisymm (le_of_not_gt hnot) hn
      rw [hzarg,Real.sin_zero,mul_zero] at he
      linarith
    have hlt : Complex.arg z<P := by
      by_contra hnot
      have hs : 0≤Real.sin (-P+Complex.arg z) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Complex.arg_le_pi z])
      rw [hrep,rotationSector_rotated_radial_im] at hrot
      exact (mul_nonneg hr.le hs).not_gt hrot
    exact ⟨‖z‖,hr,Complex.arg z,⟨ha,hlt⟩,hrep⟩

/-- Every nontrivial finite rotation has an actual sector of width at most pi. -/
theorem finiteRotationPeriod_le_pi (n : ℕ) (hn : 2≤n) : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n≤Real.pi := by
  have hn0 : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod,div_le_iff₀ hn0]
  have hnr : (2 : ℝ)≤n := by exact_mod_cast hn
  nlinarith [Real.pi_pos]

/-- The actual finite-rotation sector is a genuine intersection of two strict half-planes. -/
theorem finiteRotationPlaneSector_eq_halfPlanes (n : ℕ) (hn : 2≤n) :
    _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n = {z : ℂ | 0<z.im ∧
      ((Circle.exp (-_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n) : ℂ)*z).im<0} := by
  ext z
  exact (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector_mem_iff n z).trans
    (rotationSector_halfPlanes_iff _ (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod_pos n (by omega))
      (finiteRotationPeriod_le_pi n hn) z)

/-- Both literal side inequalities are real linear; their intersection is genuinely convex. -/
theorem rotationSector_halfPlanes_convex (P : ℝ) :
    Convex ℝ {z : ℂ | 0<z.im ∧ ((Circle.exp (-P) : ℂ)*z).im<0} := by
  have h₁ : Convex ℝ {z : ℂ | 0<z.im} :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap
  have h₂ : Convex ℝ {z : ℂ | ((Circle.exp (-P) : ℂ)*z).im<0} :=
    (convex_Iio (0 : ℝ)).linear_preimage
      (Complex.imCLM.comp (ContinuousLinearMap.mul ℝ ℂ (Circle.exp (-P) : ℂ))).toLinearMap
  exact h₁.inter h₂

theorem finiteRotationPlaneSector_convex (n : ℕ) (hn : 2≤n) :
    Convex ℝ (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n) := by
  rw [finiteRotationPlaneSector_eq_halfPlanes n hn]
  exact rotationSector_halfPlanes_convex _

/-- The actual angular region is invariant under every positive radial rescaling. -/
theorem finiteRotationPlaneSector_positive_smul {n : ℕ} {z : ℂ}
    (hz : z∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n) {c : ℝ} (hc : 0<c) :
    c • z∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n := by
  obtain ⟨r,hr,t,ht,rfl⟩ := (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector_mem_iff n
    z).mp hz
  apply (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector_mem_iff n _).mpr
  refine ⟨c*r,mul_pos hc hr,t,ht,?_⟩
  simp only [Complex.real_smul,Complex.ofReal_mul]
  ring

theorem finiteRotationPlaneSector_positive_smul_iff (n : ℕ) (z : ℂ) {c : ℝ} (hc : 0<c) :
    c • z∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n ↔ z∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n := by
  refine ⟨?_,fun hz => finiteRotationPlaneSector_positive_smul hz hc⟩
  intro hz
  have hh := finiteRotationPlaneSector_positive_smul hz (inv_pos.mpr hc)
  rwa [smul_smul,inv_mul_cancel₀ hc.ne',one_smul] at hh

/-- The actual finite-rotation sector restricted to the native hyperbolic disc. -/
def finiteRotationDiscSector (n : ℕ) : Set 𝔻 :=
  ((↑) : 𝔻 → ℂ) ⁻¹' _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n

theorem finiteRotationDiscSector_isOpen (n : ℕ) : IsOpen (finiteRotationDiscSector n) :=
  (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector_isOpen
    n).preimage Complex.UnitDisc.continuous_coe

/-- Radial Klein transport leaves the original angular sides unchanged. -/
theorem finiteRotationDiscSector_klein_image (n : ℕ) :
    kleinCoordinate '' finiteRotationDiscSector n = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n ∩ Metric.ball (0 : ℂ) 1 := by
  have he : finiteRotationDiscSector n = kleinCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n := by
    ext z
    let c : ℝ := 2 / (1 + ‖(z : ℂ)‖ ^ 2)
    have hc : 0<c := by dsimp [c];positivity
    have hK : kleinCoordinate z = c • (z : ℂ) := by
      rw [Complex.real_smul]
      rfl
    change (z : ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n ↔ kleinCoordinate z∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n
    rw [hK]
    exact (finiteRotationPlaneSector_positive_smul_iff n z hc).symm
  rw [he,image_preimage_eq_inter_range,range_kleinCoordinate]

/-- The original native sector has actual geodesic convexity, including the half-disc case n=2. -/
theorem finiteRotationDiscSector_hConvex (n : ℕ) (hn : 2≤n) :
    DiscHConvex (finiteRotationDiscSector n) := by
  apply (discHConvex_iff_klein_convex _).mpr
  rw [finiteRotationDiscSector_klein_image]
  exact (finiteRotationPlaneSector_convex n hn).inter (convex_ball _ _)

end
end LowDimensionalTopology.Geometry.Hyperbolic
