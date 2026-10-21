/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Polygon.Disk
/-! # Actual native geodesics with exact prescribed affine Klein chord equations. -/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set InnerProductGeometry
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The actual ideal endpoints of a Euclidean Klein chord at offset r and unit normal n. -/
def kleinTangentEndpointFormula (n : ℂ) (r ε : ℝ) : ℂ :=
  (⟨r,ε*Real.sqrt (1-r^2)⟩ : ℂ) * n

theorem kleinTangentEndpointFormula_norm (n : ℂ) (r ε : ℝ) (hn : ‖n‖ = 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hε : ε^2 = 1) : ‖kleinTangentEndpointFormula n r ε‖ = 1 := by
  rw [kleinTangentEndpointFormula,norm_mul,hn,mul_one]
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [Complex.sq_norm]
  have hs : Real.sqrt (1-r^2)^2 = 1-r^2 := Real.sq_sqrt (by nlinarith only [hr.1,hr.2])
  change r*r + (ε*Real.sqrt (1-r^2))*(ε*Real.sqrt (1-r^2)) = 1^2
  nlinarith only [hs,congrArg (fun t : ℝ => t * Real.sqrt (1-r^2)^2) hε]

def kleinTangentEndpoint (n : ℂ) (r ε : ℝ) (hn : ‖n‖ = 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hε : ε^2 = 1) : 𝕔𝔻 :=
  Complex.UnitClosedDisc.mk (kleinTangentEndpointFormula n r ε)
    (kleinTangentEndpointFormula_norm n r ε hn hr hε).le

theorem kleinTangentEndpoints_ne (n : ℂ) (r : ℝ) (hn : ‖n‖ = 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    kleinTangentEndpoint n r 1 hn hr (by norm_num) ≠
      kleinTangentEndpoint n r (-1) hn hr (by norm_num) := by
  intro he
  have he' := congrArg (fun p : 𝕔𝔻 => (p : ℂ)) he
  change kleinTangentEndpointFormula n r 1 = kleinTangentEndpointFormula n r (-1) at he'
  have hn0 : n ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
  have hc := mul_right_cancel₀ hn0 he'
  have hi := congrArg Complex.im hc
  simp only [one_mul,neg_one_mul] at hi
  have hs : 0 < Real.sqrt (1-r^2) := Real.sqrt_pos.mpr (by nlinarith only [hr.1,hr.2])
  linarith only [hi,hs]

/-- A genuine native geodesic obtained from its two actual ideal endpoints. -/
def kleinTangentDiscLine (n : ℂ) (r : ℝ) (hn : ‖n‖ = 1) (hr : r ∈ Ioo (0 : ℝ) 1) : DiscLine :=
  (existsUnique_discLine_closedCarrier (kleinTangentEndpoint n r 1 hn hr (by norm_num))
    (kleinTangentEndpoint n r (-1) hn hr (by norm_num)) (kleinTangentEndpoints_ne n r hn hr)).exists.choose

theorem kleinTangentDiscLine_endpoints (n : ℂ) (r : ℝ) (hn : ‖n‖ = 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    kleinTangentEndpoint n r 1 hn hr (by norm_num) ∈ (kleinTangentDiscLine n r hn hr).closedCarrier ∧
      kleinTangentEndpoint n r (-1) hn hr (by norm_num) ∈ (kleinTangentDiscLine n r hn hr).closedCarrier :=
  (existsUnique_discLine_closedCarrier (kleinTangentEndpoint n r 1 hn hr (by norm_num))
    (kleinTangentEndpoint n r (-1) hn hr (by norm_num)) (kleinTangentEndpoints_ne n r hn hr)).exists.choose_spec

theorem kleinTangentEndpoint_inner (n : ℂ) (r ε : ℝ) (hn : ‖n‖ = 1) :
    inner ℝ n (kleinTangentEndpointFormula n r ε) = r := by
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  simp only [kleinTangentEndpointFormula,Complex.mul_re,Complex.mul_im]
  have hn2 := congrArg (fun x : ℝ => x^2) hn
  rw [Complex.sq_norm] at hn2
  change n.re*n.re+n.im*n.im = 1^2 at hn2
  nlinarith only [congrArg (fun x : ℝ => r*x) hn2]

/-- The actual native line has exactly the intended normalized affine Klein equation. -/
theorem kleinTangentDiscLine_closed_equation (n : ℂ) (r : ℝ) (hn : ‖n‖ = 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (p : 𝕔𝔻)
    (hp : p ∈ (kleinTangentDiscLine n r hn hr).closedCarrier) :
    inner ℝ n (closedKleinCoordinate p) = r := by
  let a := kleinTangentEndpoint n r 1 hn hr (by norm_num)
  let b := kleinTangentEndpoint n r (-1) hn hr (by norm_num)
  have haN : ‖(a : ℂ)‖ = 1 := kleinTangentEndpointFormula_norm n r 1 hn hr (by norm_num)
  have hbN : ‖(b : ℂ)‖ = 1 := kleinTangentEndpointFormula_norm n r (-1) hn hr (by norm_num)
  have hab : a ≠ b := kleinTangentEndpoints_ne n r hn hr
  have he := closedModelDiscHSegment_ideal_endpoints (kleinTangentDiscLine n r hn hr) a b
    haN hbN hab (kleinTangentDiscLine_endpoints n r hn hr).1 (kleinTangentDiscLine_endpoints n r hn hr).2
  have hpS : closedKleinCoordinate p ∈ segment ℝ (closedKleinCoordinate a) (closedKleinCoordinate b) := by
    rw [← closedKlein_image_closedModelDiscHSegment,he]
    exact mem_image_of_mem closedKleinCoordinate hp
  have haK : closedKleinCoordinate a = (a : ℂ) :=
    congrArg (fun q : 𝕔𝔻 => (q : ℂ)) (closedPoincareToKlein_ideal_fixed a haN)
  have hbK : closedKleinCoordinate b = (b : ℂ) :=
    congrArg (fun q : 𝕔𝔻 => (q : ℂ)) (closedPoincareToKlein_ideal_fixed b hbN)
  rw [haK,hbK] at hpS
  exact (convex_hyperplane (innerSL ℝ n).toLinearMap.isLinear r).segment_subset
    (kleinTangentEndpoint_inner n r 1 hn) (kleinTangentEndpoint_inner n r (-1) hn) hpS

/-- The complete genuine closed native geodesic is precisely the intended Klein chord. -/
theorem kleinTangentDiscLine_closed_equation_iff (n : ℂ) (r : ℝ) (hn : ‖n‖ = 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (p : 𝕔𝔻) :
    p ∈ (kleinTangentDiscLine n r hn hr).closedCarrier ↔
      inner ℝ n (closedKleinCoordinate p) = r := by
  constructor
  · exact kleinTangentDiscLine_closed_equation n r hn hr p
  · intro hp
    let a := kleinTangentEndpoint n r 1 hn hr (by norm_num)
    let b := kleinTangentEndpoint n r (-1) hn hr (by norm_num)
    have haN : ‖(a : ℂ)‖ = 1 := kleinTangentEndpointFormula_norm n r 1 hn hr (by norm_num)
    have hbN : ‖(b : ℂ)‖ = 1 := kleinTangentEndpointFormula_norm n r (-1) hn hr (by norm_num)
    have hab : a ≠ b := kleinTangentEndpoints_ne n r hn hr
    have he := closedModelDiscHSegment_ideal_endpoints (kleinTangentDiscLine n r hn hr) a b
      haN hbN hab (kleinTangentDiscLine_endpoints n r hn hr).1 (kleinTangentDiscLine_endpoints n r hn hr).2
    have haK : closedKleinCoordinate a = (a : ℂ) :=
      congrArg (fun q : 𝕔𝔻 => (q : ℂ)) (closedPoincareToKlein_ideal_fixed a haN)
    have hbK : closedKleinCoordinate b = (b : ℂ) :=
      congrArg (fun q : 𝕔𝔻 => (q : ℂ)) (closedPoincareToKlein_ideal_fixed b hbN)
    have hn0 : n ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    have hsub := affine_closedDisc_subset_segment_unit_endpoints hn0
      (closedKleinCoordinate_injective.ne hab) (haK ▸ haN) (hbK ▸ hbN)
      (show inner ℝ n (closedKleinCoordinate a) = r from haK ▸ kleinTangentEndpoint_inner n r 1 hn)
      (show inner ℝ n (closedKleinCoordinate b) = r from hbK ▸ kleinTangentEndpoint_inner n r (-1) hn)
    have hpS : closedKleinCoordinate p ∈ segment ℝ (closedKleinCoordinate a) (closedKleinCoordinate b) :=
      hsub ⟨hp,mem_closedBall_zero_iff.mpr (closedPoincareToKlein p).norm_le_one⟩
    apply closedKleinCoordinate_injective.mem_set_image.mp
    rw [← he,closedKlein_image_closedModelDiscHSegment]
    exact hpS

/-- The actual finite native line has the same exact affine Klein equation. -/
theorem kleinTangentDiscLine_equation_iff (n : ℂ) (r : ℝ) (hn : ‖n‖ = 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (z : 𝔻) :
    z ∈ (kleinTangentDiscLine n r hn hr).carrier ↔ inner ℝ n (kleinCoordinate z) = r := by
  rw [← (kleinTangentDiscLine n r hn hr).closedCarrier_mem_interior_iff z,
    kleinTangentDiscLine_closed_equation_iff]
  rfl

end
end LowDimensionalTopology.Geometry.Hyperbolic
