module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.LambertQuadrilaterals
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TwoIdealTriangles
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

def lambertStandardRadius (φ : ℝ) : ℝ :=
  Real.cos φ + Real.sqrt (Real.cos φ ^ 2 + 1)

theorem lambertStandardRadius_relation (φ : ℝ) :
    lambertStandardRadius φ ^ 2 - 1 = 2 * lambertStandardRadius φ * Real.cos φ := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ Real.cos φ ^ 2 + 1)
  unfold lambertStandardRadius
  nlinarith only [hs]

theorem lambertStandardRadius_gt_one (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    1 < lambertStandardRadius φ := by
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1,Real.pi_pos],hφ.2⟩
  have hs : 1 ≤ Real.sqrt (Real.cos φ ^ 2 + 1) := by
    apply Real.one_le_sqrt.mpr
    nlinarith only [sq_nonneg (Real.cos φ)]
  unfold lambertStandardRadius
  linarith only [hc,hs]

def lambertStandardCorner (φ : ℝ) : ℂ :=
  ⟨(lambertStandardRadius φ ^ 2 + 1) / (2 * Real.sqrt 2),
    lambertStandardRadius φ * Real.sin φ / Real.sqrt 2⟩

theorem lambertStandardCorner_re_pos (φ : ℝ) : 0 < (lambertStandardCorner φ).re := by
  exact div_pos (by positivity) (by positivity)

theorem lambertStandardCorner_im_nonneg (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    0 ≤ (lambertStandardCorner φ).im := by
  exact div_nonneg (mul_nonneg (by linarith [lambertStandardRadius_gt_one φ hφ])
    (Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 (by linarith [hφ.2,Real.pi_pos]))) (Real.sqrt_nonneg 2)

theorem lambertStandardCorner_norm_sq (φ : ℝ) :
    ‖lambertStandardCorner φ‖ ^ 2 = lambertStandardRadius φ ^ 2 := by
  have hu : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : Real.sqrt 2 ≠ 0 := ne_of_gt (by positivity)
  have hrel := congrArg (fun x : ℝ => x ^ 2) (lambertStandardRadius_relation φ)
  have htrig := congrArg (fun x : ℝ => 4 * lambertStandardRadius φ ^ 2 * x) (Real.sin_sq_add_cos_sq φ)
  rw [← Complex.normSq_eq_norm_sq]
  simp only [lambertStandardCorner,Complex.normSq_apply]
  field_simp
  nlinarith only [hu,hrel,htrig]

theorem lambertStandardCorner_right_circle (φ : ℝ) :
    ‖lambertStandardCorner φ - (Real.sqrt 2 : ℂ)‖ = 1 := by
  have hnorm := lambertStandardCorner_norm_sq φ
  have hu : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : 2 * Real.sqrt 2 * (lambertStandardCorner φ).re = lambertStandardRadius φ ^ 2 + 1 := by
    change 2 * Real.sqrt 2 * ((lambertStandardRadius φ ^ 2 + 1) / (2 * Real.sqrt 2)) = _
    field_simp
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  have he := norm_sub_sq_real (lambertStandardCorner φ) (Real.sqrt 2 : ℂ)
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates] at he
  simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,add_zero] at he
  nlinarith only [he,hnorm,hu,hx]

def lambertStandardClosedCorner (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi /
  2)) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel :=
  ⟨((lambertStandardCorner φ : ℂ) : OnePoint ℂ),
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_closedHalfPlaneSet
      _).mpr (lambertStandardCorner_im_nonneg φ hφ)⟩

/-- A real-centred circle contains exactly its genuine finite arc and its two real ends. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle_closedCarrier_of_coe (c r : ℝ) (hr : 0 <
  r)
    (z : ℂ) (hz : 0 ≤ z.im) (hcircle : ‖z - (c : ℂ)‖ = r) :
    (⟨(z : OnePoint ℂ),(_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_closedHalfPlaneSet z).mpr hz⟩ :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel) ∈
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle c r hr).closedCarrier := by
  by_cases hp : 0 < z.im
  · let w : ℍ := ⟨z,hp⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel w ∈ _
    exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle c r
      hr).closedCarrier_mem_interior_iff w).mpr hcircle
  · have hzi : z.im = 0 := le_antisymm (not_lt.mp hp) hz
    apply ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle c r hr).closedCarrier_mem_ideal_iff _
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary z).mpr hzi)).mpr
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circle_idealEndpoints]
    have he : (z.re - c) ^ 2 = r ^ 2 := by
      have hs := congrArg (fun x : ℝ => x ^ 2) hcircle
      rw [← Complex.normSq_eq_norm_sq] at hs
      simpa only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
        Complex.ofReal_im,hzi,sub_zero,pow_two,zero_mul,add_zero] using hs
    have he' : z.re = c - r ∨ z.re = c + r := by
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with h | h
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    rcases he' with h | h
    · apply Or.inl
      apply congrArg (fun x : ℂ => (x : OnePoint ℂ))
      apply Complex.ext <;> simp [h,hzi]
    · apply Or.inr
      apply congrArg (fun x : ℂ => (x : OnePoint ℂ))
      apply Complex.ext <;> simp [h,hzi]

def lambertStandardA : ℍ := ⟨Complex.I,by norm_num⟩

def lambertStandardB : ℍ := ⟨⟨Real.sqrt 2 / 2,Real.sqrt 2 / 2⟩,by positivity⟩

def lambertStandardD (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) : ℍ :=
  ⟨⟨0,lambertStandardRadius φ⟩,by linarith [lambertStandardRadius_gt_one φ hφ]⟩

theorem lambertStandardB_norm : ‖(lambertStandardB : ℂ)‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← Complex.normSq_eq_norm_sq]
  simp only [lambertStandardB,Complex.normSq_apply,one_pow]
  nlinarith only [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]

theorem lambertStandardB_right_circle : ‖(lambertStandardB : ℂ) - (Real.sqrt 2 : ℂ)‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← Complex.normSq_eq_norm_sq]
  simp only [lambertStandardB,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,sub_zero,one_pow]
  nlinarith only [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_closed_points (L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) {p q :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel}
    (hpq : p ≠ q) (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier)
    (hpM : p ∈ M.closedCarrier) (hqM : q ∈ M.closedCarrier) : L = M := by
  have he := L.toDiscLine.eq_of_two_closed_points M.toDiscLine
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.injective.ne hpq)
    ((L.toDiscLine.closedCarrier_cayley_mem p).mpr (by simpa only [L.toDiscLine_toHalfPlane] using hpL))
    ((L.toDiscLine.closedCarrier_cayley_mem q).mpr (by simpa only [L.toDiscLine_toHalfPlane] using hqL))
    ((M.toDiscLine.closedCarrier_cayley_mem p).mpr (by simpa only [M.toDiscLine_toHalfPlane] using hpM))
    ((M.toDiscLine.closedCarrier_cayley_mem q).mpr (by simpa only [M.toDiscLine_toHalfPlane] using hqM))
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane] using congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane he

/-- The constructed fourth point is on the actual upper half-plane top semicircle, including its ideal ends. -/
theorem lambertStandardClosedCorner_mem_top (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    lambertStandardClosedCorner φ hφ ∈
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (lambertStandardRadius φ) (by linarith [lambertStandardRadius_gt_one φ hφ])).closedCarrier := by
  refine _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle_closedCarrier_of_coe 0 (lambertStandardRadius φ)
    (by linarith [lambertStandardRadius_gt_one φ hφ]) (lambertStandardCorner φ)
    (lambertStandardCorner_im_nonneg φ hφ) ?_
  have hR : 0 ≤ lambertStandardRadius φ := by linarith [lambertStandardRadius_gt_one φ hφ]
  simp only [Complex.ofReal_zero,sub_zero]
  exact (sq_eq_sq₀ (norm_nonneg _) hR).mp (lambertStandardCorner_norm_sq φ)

theorem lambertStandardClosedCorner_mem_right (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    lambertStandardClosedCorner φ hφ ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (Real.sqrt 2) 1 zero_lt_one).closedCarrier := by
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle_closedCarrier_of_coe (Real.sqrt
    2) 1 zero_lt_one
    (lambertStandardCorner φ) (lambertStandardCorner_im_nonneg φ hφ) (lambertStandardCorner_right_circle φ)

theorem lambertStandardClosedCorner_ne_D (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    lambertStandardClosedCorner φ hφ ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (lambertStandardD φ hφ) := by
  intro he
  have hc := congrArg Complex.re (OnePoint.coe_injective (congrArg Subtype.val he))
  change (lambertStandardCorner φ).re = 0 at hc
  exact (lambertStandardCorner_re_pos φ).ne' hc

theorem lambertStandardClosedCorner_ne_B (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    lambertStandardClosedCorner φ hφ ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel lambertStandardB := by
  intro he
  have hc := congrArg norm (OnePoint.coe_injective (congrArg Subtype.val he))
  change ‖lambertStandardCorner φ‖ = ‖(lambertStandardB : ℂ)‖ at hc
  rw [lambertStandardB_norm] at hc
  have hn := lambertStandardCorner_norm_sq φ
  rw [hc,one_pow] at hn
  nlinarith only [hn,lambertStandardRadius_gt_one φ hφ]

theorem lambertStandardD_norm (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    ‖(lambertStandardD φ hφ : ℂ)‖ = lambertStandardRadius φ := by
  rw [show (lambertStandardD φ hφ : ℂ) = (lambertStandardRadius φ : ℂ) * Complex.I by
    apply Complex.ext <;> simp [lambertStandardD],norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,mul_one,abs_of_pos (by linarith [lambertStandardRadius_gt_one φ hφ])]

/-- The actual corner triangle is noncollinear in the genuine compactified H model. -/
def lambertStandardHTriangle (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi /
  2)) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle where
  a := lambertStandardClosedCorner φ hφ
  b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (lambertStandardD φ hφ)
  c := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel lambertStandardB
  noncollinear := by
    rintro ⟨L,hC,hD,hB⟩
    let M := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (lambertStandardRadius φ) (by linarith [lambertStandardRadius_gt_one φ hφ])
    have hDM : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (lambertStandardD φ hφ) ∈ M.closedCarrier := by
      apply (M.closedCarrier_mem_interior_iff _).mpr
      change ‖(lambertStandardD φ hφ : ℂ) - (0 : ℂ)‖ = _
      rw [sub_zero,lambertStandardD_norm]
    have he : L = M := L.eq_of_two_closed_points M (lambertStandardClosedCorner_ne_D φ hφ)
      hC hD (lambertStandardClosedCorner_mem_top φ hφ) hDM
    rw [he] at hB
    have hn := (M.closedCarrier_mem_interior_iff lambertStandardB).mp hB
    change ‖(lambertStandardB : ℂ) - (0 : ℂ)‖ = lambertStandardRadius φ at hn
    rw [sub_zero,lambertStandardB_norm] at hn
    exact (lambertStandardRadius_gt_one φ hφ).ne hn

def lambertStandardTriangle (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi /
  2)) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle :=
  (lambertStandardHTriangle φ hφ).toDiscTriangle

theorem lambertStandardTriangle_vertex_D (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    (lambertStandardTriangle φ hφ).b = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (lambertStandardD φ hφ)) := by
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior _

theorem lambertStandardTriangle_vertex_B (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    (lambertStandardTriangle φ hφ).c = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc lambertStandardB) := by
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior _

theorem lambertStandardTriangle_right_side (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    (lambertStandardTriangle φ hφ).sideLineB.toHalfPlane = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (Real.sqrt 2) 1 zero_lt_one := by
  let T := lambertStandardTriangle φ hφ
  let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (Real.sqrt 2) 1 zero_lt_one
  have hC : lambertStandardClosedCorner φ hφ ∈ T.sideLineB.toHalfPlane.closedCarrier :=
    (T.sideLineB.closedCarrier_cayley_mem _).mp T.a_mem_sideLineB
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel lambertStandardB ∈ T.sideLineB.toHalfPlane.closedCarrier :=
    (T.sideLineB.closedCarrier_cayley_mem _).mp T.c_mem_sideLineB
  have hBL : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel lambertStandardB ∈ L.closedCarrier :=
    (L.closedCarrier_mem_interior_iff _).mpr lambertStandardB_right_circle
  exact T.sideLineB.toHalfPlane.eq_of_two_closed_points L (lambertStandardClosedCorner_ne_B φ hφ)
    hC hB (lambertStandardClosedCorner_mem_right φ hφ) hBL

theorem lambertStandardTriangle_top_side (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    (lambertStandardTriangle φ hφ).sideLineC.toHalfPlane =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (lambertStandardRadius φ) (by linarith [lambertStandardRadius_gt_one φ hφ]) := by
  let T := lambertStandardTriangle φ hφ
  let M := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (lambertStandardRadius φ) (by linarith [lambertStandardRadius_gt_one φ hφ])
  have hC : lambertStandardClosedCorner φ hφ ∈ T.sideLineC.toHalfPlane.closedCarrier :=
    (T.sideLineC.closedCarrier_cayley_mem _).mp T.a_mem_sideLineC
  have hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (lambertStandardD φ
    hφ) ∈ T.sideLineC.toHalfPlane.closedCarrier :=
    (T.sideLineC.closedCarrier_cayley_mem _).mp T.b_mem_sideLineC
  have hDM : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (lambertStandardD φ hφ) ∈ M.closedCarrier := by
    apply (M.closedCarrier_mem_interior_iff _).mpr
    change ‖(lambertStandardD φ hφ : ℂ) - (0 : ℂ)‖ = _
    rw [sub_zero,lambertStandardD_norm]
  exact T.sideLineC.toHalfPlane.eq_of_two_closed_points M (lambertStandardClosedCorner_ne_D φ hφ)
    hC hD (lambertStandardClosedCorner_mem_top φ hφ) hDM

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closed_affine_halfPlane (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine L.incenterNormal L.incenterOffset
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine L.toHalfPlane.incenterNormal L.toHalfPlane.incenterOffset z := by
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.incenterNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.incenterOffset,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate]

theorem lambertStandardRight_affine_axis (z : ℍ) (hz : z.re = 0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (Real.sqrt 2) 1 zero_lt_one).incenterNormal
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (Real.sqrt 2) 1 zero_lt_one).incenterOffset z = 1 := by
  have hu : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.incenterNormal,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.incenterOffset,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,hz,hu]
  ring

theorem halfPlaneCircle_affine_of_norm_one (R : ℝ) (hR : 0 < R) (z : ℍ) (hz : ‖(z : ℂ)‖ = 1) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 R hR).incenterNormal
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 R hR).incenterOffset z = (1 - R ^ 2) / (2 * R) := by
  have he : z.re ^ 2 + z.im ^ 2 = 1 := by
    have hsq := Complex.normSq_eq_norm_sq (z : ℂ)
    rw [hz,one_pow] at hsq
    simpa only [Complex.normSq_apply,pow_two,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im] using hsq
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleLine_incenter_affine,Complex.ofReal_zero,sub_zero,hz,one_pow,he]
  ring

theorem lambertStandardTriangle_coordinate_A (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    (lambertStandardTriangle φ hφ).discCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc lambertStandardA) = (1,1) := by
  let T := lambertStandardTriangle φ hφ
  let a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc lambertStandardA
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset
  let G := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset
  let δ := (1 - lambertStandardRadius φ ^ 2) / (2 * lambertStandardRadius φ)
  have hFa : F (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a) = 1 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (lambertStandardTriangle φ
      hφ).sideLineB.incenterNormal
      (lambertStandardTriangle φ hφ).sideLineB.incenterOffset
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc lambertStandardA)) = 1
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closed_affine_halfPlane,lambertStandardTriangle_right_side]
    exact lambertStandardRight_affine_axis lambertStandardA rfl
  have hFb : F T.b = 1 := by
    change F (lambertStandardTriangle φ hφ).b = 1
    rw [lambertStandardTriangle_vertex_D]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (lambertStandardTriangle φ
      hφ).sideLineB.incenterNormal
      (lambertStandardTriangle φ hφ).sideLineB.incenterOffset
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (lambertStandardD φ hφ))) = 1
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closed_affine_halfPlane,lambertStandardTriangle_right_side]
    exact lambertStandardRight_affine_axis (lambertStandardD φ hφ) rfl
  have hGa : G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a) = δ := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (lambertStandardTriangle φ
      hφ).sideLineC.incenterNormal
      (lambertStandardTriangle φ hφ).sideLineC.incenterOffset
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc lambertStandardA)) = δ
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closed_affine_halfPlane,lambertStandardTriangle_top_side]
    exact halfPlaneCircle_affine_of_norm_one _ _ lambertStandardA (by exact Complex.norm_I)
  have hGc : G T.c = δ := by
    change G (lambertStandardTriangle φ hφ).c = δ
    rw [lambertStandardTriangle_vertex_B]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (lambertStandardTriangle φ
      hφ).sideLineC.incenterNormal
      (lambertStandardTriangle φ hφ).sideLineC.incenterOffset
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc lambertStandardB)) = δ
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closed_affine_halfPlane,lambertStandardTriangle_top_side]
    exact halfPlaneCircle_affine_of_norm_one _ _ lambertStandardB lambertStandardB_norm
  have hFC : F T.a = 0 := (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineB
  have hFB : F T.c = 0 := (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.c_mem_sideLineB
  have hGC : G T.a = 0 := (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineC
  have hGD : G T.b = 0 := (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.b_mem_sideLineC
  have hx := T.kleinAffine_reconstruction T.sideLineB.incenterNormal T.sideLineB.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a)
  change F (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a) =
    (1 - (T.discCoordinate a).1 - (T.discCoordinate a).2) * F T.a +
      (T.discCoordinate a).1 * F T.b + (T.discCoordinate a).2 * F T.c at hx
  rw [hFa,hFC,hFb,hFB] at hx
  have hy := T.kleinAffine_reconstruction T.sideLineC.incenterNormal T.sideLineC.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a)
  change G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a) =
    (1 - (T.discCoordinate a).1 - (T.discCoordinate a).2) * G T.a +
      (T.discCoordinate a).1 * G T.b + (T.discCoordinate a).2 * G T.c at hy
  rw [hGa,hGC,hGD,hGc] at hy
  have hδ : δ ≠ 0 := by
    apply div_ne_zero
    · nlinarith only [lambertStandardRadius_gt_one φ hφ]
    · have hR := lambertStandardRadius_gt_one φ hφ
      positivity
  apply Prod.ext
  · nlinarith only [hx]
  · apply mul_left_cancel₀ hδ
    nlinarith only [hy]

theorem lambertStandard_three_right_angles (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1
      zero_lt_one).OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
      0) lambertStandardA ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one).OrthogonalAt
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (Real.sqrt 2) 1
        zero_lt_one) lambertStandardB ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).OrthogonalAt
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (lambertStandardRadius φ) (by linarith [lambertStandardRadius_gt_one φ hφ]))
        (lambertStandardD φ hφ) := by
  have hA : lambertStandardA ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one).carrier := by
    change ‖Complex.I - (0 : ℂ)‖ = 1
    rw [sub_zero,Complex.norm_I]
  have hB : lambertStandardB ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one).carrier := by
    change ‖(lambertStandardB : ℂ) - (0 : ℂ)‖ = 1
    rw [sub_zero,lambertStandardB_norm]
  have hD : lambertStandardD φ hφ ∈
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (lambertStandardRadius φ) (by linarith [lambertStandardRadius_gt_one φ hφ])).carrier := by
    change ‖(lambertStandardD φ hφ : ℂ) - (0 : ℂ)‖ = _
    rw [sub_zero,lambertStandardD_norm]
  refine ⟨?_,?_,?_⟩
  · exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1
    zero_lt_one).orthogonalAt_iff_coefficients
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0) lambertStandardA hA rfl).mpr rfl
  · apply ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1
    zero_lt_one).orthogonalAt_iff_coefficients
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (Real.sqrt 2) 1
        zero_lt_one) lambertStandardB hB lambertStandardB_right_circle).mpr
    change (0 - Real.sqrt 2) ^ 2 = 1 ^ 2 + 1 ^ 2
    nlinarith only [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  · exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).orthogonalAt_iff_coefficients
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (lambertStandardRadius φ) (by linarith [lambertStandardRadius_gt_one φ hφ]))
      (lambertStandardD φ hφ) rfl hD).mpr rfl

/-- Explicit actual three-right-angle quadrilateral, with the zero-angle ideal endpoint retained. -/
def lambertQuadrilateralOfAngle (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) : LambertQuadrilateral where
  corner := lambertStandardTriangle φ hφ
  a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc lambertStandardA
  b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc lambertStandardB
  d := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (lambertStandardD φ hφ)
  vertex_d := lambertStandardTriangle_vertex_D φ hφ
  vertex_b := lambertStandardTriangle_vertex_B φ hφ
  bottom := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one).toDiscLine
  left := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).toDiscLine
  angle_a := by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.orthogonalAt_iff_halfPlane _ _ _).mpr
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using
      (lambertStandard_three_right_angles φ hφ).1
  angle_b := by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.orthogonalAt_iff_halfPlane _ _ _).mpr
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane,lambertStandardTriangle_right_side,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
    exact (lambertStandard_three_right_angles φ hφ).2.1
  angle_d := by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.orthogonalAt_iff_halfPlane _ _ _).mpr
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane,lambertStandardTriangle_top_side,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
    exact (lambertStandard_three_right_angles φ hφ).2.2
  convex_corner := by
    rw [lambertStandardTriangle_coordinate_A]
    exact ⟨zero_lt_one,zero_lt_one⟩
  opposite_chord := by
    rw [lambertStandardTriangle_coordinate_A]
    norm_num

theorem lambertStandard_side_distance_sinh_right :
    Real.sinh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (Real.sqrt 2) 1 zero_lt_one).pointDist lambertStandardA) = 1 := by
  have hu : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : ‖(lambertStandardA : ℂ) - (Real.sqrt 2 : ℂ)‖ ^ 2 = 3 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [lambertStandardA,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero,zero_sub]
    nlinarith only [hu]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleLine_pointDist_sinh,hn]
  norm_num [lambertStandardA]

theorem lambertStandard_side_distance_sinh_top (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    Real.sinh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (lambertStandardRadius φ)
      (by linarith [lambertStandardRadius_gt_one φ hφ])).pointDist lambertStandardA) = Real.cos φ := by
  have hR := lambertStandardRadius_gt_one φ hφ
  have hn : 1 - lambertStandardRadius φ ^ 2 < 0 := by nlinarith only [hR]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleLine_pointDist_sinh,Complex.ofReal_zero,sub_zero]
  change |‖Complex.I‖ ^ 2 - lambertStandardRadius φ ^ 2| /
    (2 * 1 * lambertStandardRadius φ) = _
  rw [Complex.norm_I,one_pow,abs_of_neg hn]
  have hp : lambertStandardRadius φ ≠ 0 := ne_of_gt (by linarith only [hR])
  field_simp
  nlinarith only [lambertStandardRadius_relation φ]

theorem lambertQuadrilateralOfAngle_angle (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    (lambertQuadrilateralOfAngle φ hφ).angle = φ := by
  let Q := lambertQuadrilateralOfAngle φ hφ
  have he := Q.sinh_side_distances
  change Real.sinh ((lambertStandardTriangle φ hφ).sideLineB.pointDist
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc lambertStandardA)) *
    Real.sinh ((lambertStandardTriangle φ hφ).sideLineC.pointDist
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc lambertStandardA)) =
      Real.cos Q.angle at he
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.pointDist_eq_halfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.pointDist_eq_halfPlane,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,lambertStandardTriangle_right_side,lambertStandardTriangle_top_side,
    lambertStandard_side_distance_sinh_right,lambertStandard_side_distance_sinh_top φ hφ,one_mul] at he
  have ha := Q.angle_mem_Ico
  exact Real.injOn_cos ⟨ha.1,by linarith [ha.2,Real.pi_pos]⟩
    ⟨hφ.1,by linarith [hφ.2,Real.pi_pos]⟩ he.symm

/-- Every allowed fourth angle, including zero, has an actual native Lambert quadrilateral. -/
theorem exists_lambertQuadrilateral_angle (φ : ℝ) (hφ : φ ∈ Ico (0 : ℝ) (Real.pi / 2)) :
    ∃ Q : LambertQuadrilateral, Q.angle = φ :=
  ⟨lambertQuadrilateralOfAngle φ hφ,lambertQuadrilateralOfAngle_angle φ hφ⟩

/-- The complete sharp angle range for genuine finite/ideal Lambert quadrilaterals. -/
theorem lambertQuadrilateral_angle_exists_iff (φ : ℝ) :
    (∃ Q : LambertQuadrilateral, Q.angle = φ) ↔ φ ∈ Ico (0 : ℝ) (Real.pi / 2) := by
  constructor
  · rintro ⟨Q,rfl⟩
    exact Q.angle_mem_Ico
  · exact exists_lambertQuadrilateral_angle φ

/-- The ideal endpoint is exactly the zero-angle branch of an actual Lambert configuration. -/
theorem LambertQuadrilateral.fourth_ideal_iff_angle_zero (Q : LambertQuadrilateral) :
    ‖(Q.corner.a : ℂ)‖ = 1 ↔ Q.angle = 0 := by
  constructor
  · exact Q.corner.alpha_of_ideal
  · intro hzero
    by_contra hn
    have hfinite : ‖(Q.corner.a : ℂ)‖ < 1 := lt_of_le_of_ne Q.corner.a.norm_le_one hn
    have hpos := Q.corner.alpha_bounds_of_finite (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint Q.corner.a hfinite)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec Q.corner.a hfinite).symm
    change 0 < Q.angle ∧ Q.angle < Real.pi at hpos
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos.1

/-- The positive-angle condition is exactly the mathematically necessary finite-vertex condition. -/
theorem LambertQuadrilateral.angle_pos_iff_fourth_finite (Q : LambertQuadrilateral) :
    0 < Q.angle ↔ ‖(Q.corner.a : ℂ)‖ < 1 := by
  constructor
  · intro hpos
    apply lt_of_le_of_ne Q.corner.a.norm_le_one
    intro he
    rw [Q.fourth_ideal_iff_angle_zero.mp he] at hpos
    exact lt_irrefl 0 hpos
  · intro hfinite
    exact (Q.corner.alpha_bounds_of_finite (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint
      Q.corner.a hfinite)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec Q.corner.a hfinite).symm).1

/-- The second source formula has an actual finite side whenever the fourth angle is positive. -/
theorem LambertQuadrilateral.exists_finite_corner_and_cosh_side_eq_cosh_opposite_mul_sin (Q : LambertQuadrilateral)
    (hpos : 0 < Q.angle) :
    ∃ w : 𝔻, Q.corner.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w ∧
      Real.cosh Q.sideA₁ = Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist Q.d w) * Real.sin Q.angle := by
  let w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint Q.corner.a (Q.angle_pos_iff_fourth_finite.mp hpos)
  have hw : Q.corner.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ _).symm
  exact ⟨w,hw,Q.cosh_side_eq_cosh_opposite_mul_sin w hw⟩

end
end LowDimensionalTopology.Geometry.Polygon
