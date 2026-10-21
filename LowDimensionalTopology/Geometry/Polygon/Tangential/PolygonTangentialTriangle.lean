/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.Tangential.PolygonTangentialCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicNormalCoordinates
/-! # Actual prescribed tangential corners and their true radius

The constructed genuine triangle has exactly the prescribed finite or ideal corner.
Its genuine tangent sides touch the actual radius-d hyperbolic ball at unique feet.
The ordered polygon formed by joining these corners remains a separate construction.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set InnerProductGeometry
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The prescribed vertex lies strictly beyond the segment joining its two tangent feet. -/
theorem polygonTangentialFoot_gap {θ d : ℝ} (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    0 < polygonTangentialVertexCoordinate θ d - Real.tanh d * Real.cos (polygonTangentialHalfAngle θ d) := by
  have hα := polygonTangentialHalfAngle_bounds hθ hd
  have hc := polygonTangentialHalfAngle_cos_pos hθ hd
  have hs : 0 < Real.sin (polygonTangentialHalfAngle θ d) := Real.sin_pos_of_pos_of_lt_pi hα.1
    (by linarith only [hα.2,Real.pi_pos])
  have he : polygonTangentialVertexCoordinate θ d - Real.tanh d * Real.cos (polygonTangentialHalfAngle θ d) =
      Real.tanh d * Real.sin (polygonTangentialHalfAngle θ d)^2 / Real.cos (polygonTangentialHalfAngle θ d) := by
    unfold polygonTangentialVertexCoordinate
    field_simp
    nlinarith only [congrArg (fun t : ℝ => Real.tanh d * t)
      (Real.sin_sq_add_cos_sq (polygonTangentialHalfAngle θ d))]
  rw [he]
  exact div_pos (mul_pos (polygonTangential_tanh_pos hd) (sq_pos_of_pos hs)) hc

/-- A genuine finite-or-ideal triangle at a single prescribed tangential corner. -/
def polygonTangentialTriangle (θ d : ℝ) (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 <
  d) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := polygonTangentialDiscVertex θ d hθ hd
  b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (polygonTangentialFoot θ d 1 hd (by norm_num))
  c := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (polygonTangentialFoot θ d (-1) hd (by norm_num))
  noncollinear := by
    rintro ⟨L,hA,hB,hC⟩
    obtain ⟨n,t,hn,hL⟩ := L.closedKlein_affine_equation
    have hAn := (hL _).mp hA
    have hBn := (hL _).mp hB
    have hCn := (hL _).mp hC
    rw [polygonTangentialDiscVertex_coordinate] at hAn
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,polygonTangentialFoot_coordinate] at hBn hCn
    simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.ofReal_re,Complex.ofReal_im,mul_zero,add_zero,
      Complex.smul_re,Complex.smul_im,smul_eq_mul,polygonTangentialNormal,one_mul,neg_one_mul] at hAn hBn hCn
    have hα := polygonTangentialHalfAngle_bounds hθ hd
    have hs : 0 < Real.sin (polygonTangentialHalfAngle θ d) := Real.sin_pos_of_pos_of_lt_pi hα.1
      (by linarith only [hα.2,Real.pi_pos])
    have himprod : n.im * (Real.tanh d * Real.sin (polygonTangentialHalfAngle θ d)) = 0 := by
      nlinarith only [hBn,hCn]
    have him : n.im = 0 := (mul_eq_zero.mp himprod).resolve_right
      (mul_ne_zero (polygonTangential_tanh_pos hd).ne' hs.ne')
    have hreprod : n.re * (polygonTangentialVertexCoordinate θ d -
        Real.tanh d * Real.cos (polygonTangentialHalfAngle θ d)) = 0 := by
      rw [him] at hBn
      nlinarith only [hAn,hBn]
    have hre : n.re = 0 := (mul_eq_zero.mp hreprod).resolve_right (polygonTangentialFoot_gap hθ hd).ne'
    apply hn
    exact Complex.ext hre him

/-- The origin belongs to the true positive corner cone, including when its apex is ideal. -/
theorem polygonTangentialTriangle_origin_coordinates (θ d : ℝ)
    (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    0 < ((polygonTangentialTriangle θ d hθ hd).discCoordinate (0 : 𝔻)).1 ∧
      0 < ((polygonTangentialTriangle θ d hθ hd).discCoordinate (0 : 𝔻)).2 ∧
      1 < ((polygonTangentialTriangle θ d hθ hd).discCoordinate (0 : 𝔻)).1 +
        ((polygonTangentialTriangle θ d hθ hd).discCoordinate (0 : 𝔻)).2 := by
  let T := polygonTangentialTriangle θ d hθ hd
  let x := (T.discCoordinate (0 : 𝔻)).1
  let y := (T.discCoordinate (0 : 𝔻)).2
  have he := T.klein_reconstruction (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 : 𝔻))
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 : 𝔻)) =
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (polygonTangentialDiscVertex θ d hθ hd) +
      x • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (polygonTangentialFoot θ d 1 hd (by norm_num))) -
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (polygonTangentialDiscVertex θ d hθ
          hd)) +
      y • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (polygonTangentialFoot θ d (-1) hd (by norm_num))) -
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (polygonTangentialDiscVertex θ d hθ
          hd)) at he
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,polygonTangentialDiscVertex_coordinate,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,polygonTangentialFoot_coordinate,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,polygonTangentialFoot_coordinate] at he
  have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : 𝔻) = 0 := by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  rw [hz] at he
  have hRe := congrArg Complex.re he
  have hIm := congrArg Complex.im he
  simp only [Complex.zero_re,Complex.zero_im,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.smul_re,Complex.smul_im,Complex.ofReal_re,Complex.ofReal_im,smul_eq_mul,
    polygonTangentialNormal,one_mul,neg_one_mul,sub_zero] at hRe hIm
  have hα := polygonTangentialHalfAngle_bounds hθ hd
  have hs : 0 < Real.sin (polygonTangentialHalfAngle θ d) := Real.sin_pos_of_pos_of_lt_pi hα.1
    (by linarith only [hα.2,Real.pi_pos])
  have hr := polygonTangential_tanh_pos hd
  have hgap := polygonTangentialFoot_gap hθ hd
  have hv := polygonTangentialVertexCoordinate_pos hθ hd
  have hxy : x = y := by
    have hp : (x-y) * (Real.tanh d * Real.sin (polygonTangentialHalfAngle θ d)) = 0 := by
      nlinarith only [hIm]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (mul_ne_zero hr.ne' hs.ne'))
  have hprod : x * (2*(polygonTangentialVertexCoordinate θ d - Real.tanh d *
      Real.cos (polygonTangentialHalfAngle θ d))) = polygonTangentialVertexCoordinate θ d := by
    have hxRe := hRe
    rw [← hxy] at hxRe
    nlinarith only [hxRe]
  have hx : 0 < x := pos_of_mul_pos_left (hprod.symm ▸ hv) (by positivity)
  have hsumprod : (x+y-1) * (polygonTangentialVertexCoordinate θ d - Real.tanh d *
      Real.cos (polygonTangentialHalfAngle θ d)) = Real.tanh d * Real.cos (polygonTangentialHalfAngle θ d) := by
    nlinarith only [hRe]
  have hsum : 0 < x+y-1 := pos_of_mul_pos_left (hsumprod.symm ▸
    mul_pos hr (polygonTangentialHalfAngle_cos_pos hθ hd)) hgap.le
  have hy : 0 < y := by rw [← hxy]; exact hx
  exact ⟨hx,hy,by linarith only [hsum]⟩

theorem polygonTangentialTriangle_sideB (θ d : ℝ) (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    (polygonTangentialTriangle θ d hθ hd).sideLineB = polygonTangentialSide θ d (-1) hd (by norm_num) := by
  let T := polygonTangentialTriangle θ d hθ hd
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.eq_of_two_closed_points _ _ T.c_ne_a T.c_mem_sideLineB T.a_mem_sideLineB
  · exact ((polygonTangentialSide θ d (-1) hd (by norm_num)).closedCarrier_mem_interior_iff _).mpr
      (polygonTangentialFoot_mem_side θ d (-1) hd (by norm_num))
  · exact polygonTangentialSide_vertex θ d (-1) hθ hd (by norm_num)

theorem polygonTangentialTriangle_sideC (θ d : ℝ) (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    (polygonTangentialTriangle θ d hθ hd).sideLineC = polygonTangentialSide θ d 1 hd (by norm_num) := by
  let T := polygonTangentialTriangle θ d hθ hd
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.eq_of_two_closed_points _ _ T.a_ne_b T.a_mem_sideLineC T.b_mem_sideLineC
  · exact polygonTangentialSide_vertex θ d 1 hθ hd (by norm_num)
  · exact ((polygonTangentialSide θ d 1 hd (by norm_num)).closedCarrier_mem_interior_iff _).mpr
      (polygonTangentialFoot_mem_side θ d 1 hd (by norm_num))

/-- The constructed genuine corner has exactly the prescribed actual finite-or-ideal angle. -/
theorem polygonTangentialTriangle_alpha (θ d : ℝ) (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    (polygonTangentialTriangle θ d hθ hd).alpha = θ := by
  let T := polygonTangentialTriangle θ d hθ hd
  let n := -(Real.cosh d • polygonTangentialNormal θ d (-1))
  let m := -(Real.cosh d • polygonTangentialNormal θ d 1)
  have hn : ‖n‖^2 - (-Real.sinh d)^2 = 1 := by
    rw [norm_neg,neg_sq]
    exact polygonTangentialSide_lorentz_unit θ d (-1) (by norm_num)
  have hm : ‖m‖^2 - (-Real.sinh d)^2 = 1 := by
    rw [norm_neg,neg_sq]
    exact polygonTangentialSide_lorentz_unit θ d 1 (by norm_num)
  have hB (z : 𝔻) (hz : z ∈ T.sideLineB.carrier) : inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = -Real.sinh d := by
    change z ∈ (polygonTangentialTriangle θ d hθ hd).sideLineB.carrier at hz
    rw [polygonTangentialTriangle_sideB] at hz
    rw [inner_neg_left,polygonTangentialSide_lorentz_equation θ d (-1) hd (by norm_num) z hz]
  have hC (z : 𝔻) (hz : z ∈ T.sideLineC.carrier) : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = -Real.sinh d := by
    change z ∈ (polygonTangentialTriangle θ d hθ hd).sideLineC.carrier at hz
    rw [polygonTangentialTriangle_sideC] at hz
    rw [inner_neg_left,polygonTangentialSide_lorentz_equation θ d 1 hd (by norm_num) z hz]
  have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : 𝔻) = 0 := by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  have hqn : 0 < inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : 𝔻)) - (-Real.sinh d) := by
    rw [hz,inner_zero_right,sub_neg_eq_add,zero_add]
    exact Real.sinh_pos_iff.mpr hd
  have hqm : 0 < inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : 𝔻)) - (-Real.sinh d) := by
    rw [hz,inner_zero_right,sub_neg_eq_add,zero_add]
    exact Real.sinh_pos_iff.mpr hd
  have hq := polygonTangentialTriangle_origin_coordinates θ d hθ hd
  have he := T.cosine_alpha_inward_normalized_equations (0 : 𝔻) n m (-Real.sinh d) (-Real.sinh d)
    ⟨hq.1,hq.2.1⟩ hn hm hB hC hqn hqm
  have hp : inner ℝ n m - (-Real.sinh d)*(-Real.sinh d) = -Real.cos θ := by
    dsimp only [n,m]
    rw [inner_neg_left,inner_neg_right,neg_neg,neg_mul_neg,real_inner_comm]
    nlinarith only [polygonTangentialSide_normal_pair (d := d) hθ]
  have hc : Real.cos T.alpha = Real.cos θ := by linarith only [he,hp]
  exact Real.strictAntiOn_cos.injOn ⟨T.alpha_mem_Ico.1,T.alpha_mem_Ico.2.le⟩ ⟨hθ.1,hθ.2.le⟩ hc

/-- The actual weighted radial distance is detected by the genuine Klein radius. -/
theorem kleinCoordinate_norm_eq_tanh_distance (z : 𝔻) :
    ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z‖ = Real.tanh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z) := by
  change ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z‖ = _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_norm]
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_norm_eq_tanh_half_distance]
  conv_rhs => rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z = 2*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z/2) by ring,
    Real.tanh_eq_sinh_div_cosh,Real.sinh_two_mul,Real.cosh_two_mul]
  simp only [Real.tanh_eq_sinh_div_cosh]
  have hc := Real.cosh_pos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z/2)
  have hden : 0 < Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0
    z/2)^2 + Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z/2)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg _)
  field_simp

/-- The finite tangency foot lies at exactly the requested genuine hyperbolic radius. -/
theorem polygonTangentialFoot_distance (θ d ε : ℝ) (hd : 0 < d) (hε : ε^2 = 1) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (polygonTangentialFoot θ d ε hd hε) = d := by
  apply Real.tanh_injective
  rw [← kleinCoordinate_norm_eq_tanh_distance,polygonTangentialFoot_coordinate,norm_smul,
    Real.norm_eq_abs,abs_of_pos (polygonTangential_tanh_pos hd),
    polygonTangentialNormal_norm θ d ε hε,mul_one]

/-- Every point of each actual tangent side lies outside the actual open radius-d ball. -/
theorem polygonTangentialSide_distance_lower (θ d ε : ℝ) (hd : 0 < d) (hε : ε^2 = 1)
    (z : 𝔻) (hz : z ∈ (polygonTangentialSide θ d ε hd hε).carrier) : d ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z := by
  have he := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_equation_iff _ _ _ _ z).mp hz
  have hle : Real.tanh d ≤ ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z‖ := by
    calc
      Real.tanh d = inner ℝ (polygonTangentialNormal θ d
        ε) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) := he.symm
      _ ≤ ‖polygonTangentialNormal θ d ε‖ * ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z‖ := real_inner_le_norm _ _
      _ = ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z‖ := by rw [polygonTangentialNormal_norm θ d ε hε,one_mul]
  rw [kleinCoordinate_norm_eq_tanh_distance] at hle
  have h := (Real.artanh_le_artanh_iff
    (show Real.tanh d ∈ Ioo (-1 : ℝ) 1 from ⟨Real.neg_one_lt_tanh d,Real.tanh_lt_one d⟩)
    (show Real.tanh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z) ∈ Ioo (-1 : ℝ) 1 from
      ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩)).mpr hle
  simpa only [Real.artanh_tanh] using h

theorem polygonTangentialFoot_minimizes (θ d ε : ℝ) (hd : 0 < d) (hε : ε^2 = 1)
    (z : 𝔻) (hz : z ∈ (polygonTangentialSide θ d ε hd hε).carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (polygonTangentialFoot θ d ε hd hε) ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z := by
  rw [polygonTangentialFoot_distance]
  exact polygonTangentialSide_distance_lower θ d ε hd hε z hz

/-- Contact with the actual radius-d sphere occurs at precisely the constructed finite foot. -/
theorem polygonTangentialFoot_unique (θ d ε : ℝ) (hd : 0 < d) (hε : ε^2 = 1)
    (z : 𝔻) (hz : z ∈ (polygonTangentialSide θ d ε hd hε).carrier)
    (hdz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z = d) : z = polygonTangentialFoot θ d ε hd hε := by
  have he := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_equation_iff _ _ _ _ z).mp hz
  have hn : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z‖ = Real.tanh d := by rw [kleinCoordinate_norm_eq_tanh_distance,hdz]
  have hdiff : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z - Real.tanh d • polygonTangentialNormal θ d ε‖^2 = 0 := by
    rw [norm_sub_sq_real,hn,norm_smul,Real.norm_eq_abs,abs_of_pos (polygonTangential_tanh_pos hd),
      polygonTangentialNormal_norm θ d ε hε,mul_one,real_inner_smul_right,real_inner_comm,he]
    ring
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective
  rw [polygonTangentialFoot_coordinate]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdiff))

end
end LowDimensionalTopology.Geometry.Polygon
