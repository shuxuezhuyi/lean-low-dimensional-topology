/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonAngleBalance
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.KleinTangentLines
/-! # Actual tangential-corner coordinates for prescribed polygon angles

These lemmas construct individual genuine finite or ideal vertices, finite tangent feet
and native tangent geodesics. Joining these corners into an ordered Jordan polygon
with the requested angles and incircle is a separate unfinished construction.
-/

@[expose] public section
open Set
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The half-gap between adjacent outward normal directions in the prescribed-angle construction. -/
def polygonTangentialHalfAngle (θ d : ℝ) : ℝ :=
  Real.arcsin (Real.cos (θ/2) / Real.cosh d)

theorem polygonTangentialHalfAngle_bounds {θ d : ℝ} (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    polygonTangentialHalfAngle θ d ∈ Ioo (0 : ℝ) (Real.pi/2) := by
  have hc : 0 < Real.cos (θ/2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hθ.1,Real.pi_pos],by linarith only [hθ.2]⟩
  have hcosh : 1 < Real.cosh d := by
    have he := Real.cosh_strictMonoOn (show (0 : ℝ) ∈ Ici 0 from le_rfl) hd.le hd
    simpa only [Real.cosh_zero] using he
  exact ⟨Real.arcsin_pos.mpr (div_pos hc (Real.cosh_pos d)),Real.arcsin_lt_pi_div_two.mpr
    ((div_lt_one (Real.cosh_pos d)).mpr ((Real.cos_le_one _).trans_lt hcosh))⟩

theorem polygonTangentialHalfAngle_sin {θ d : ℝ} (hθ : θ ∈ Ico (0 : ℝ) Real.pi) :
    Real.sin (polygonTangentialHalfAngle θ d) = Real.cos (θ/2) / Real.cosh d := by
  apply Real.sin_arcsin
  · have hc : 0 < Real.cos (θ/2) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [hθ.1,Real.pi_pos],by linarith only [hθ.2]⟩
    exact (by norm_num : (-1 : ℝ) ≤ 0).trans (div_pos hc (Real.cosh_pos d)).le
  · exact (div_le_one (Real.cosh_pos d)).mpr ((Real.cos_le_one _).trans (Real.one_le_cosh d))

theorem polygonTangentialHalfAngle_cos_pos {θ d : ℝ} (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    0 < Real.cos (polygonTangentialHalfAngle θ d) := by
  have hα := polygonTangentialHalfAngle_bounds hθ hd
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith only [hα.1,Real.pi_pos],hα.2⟩

/-- The real Klein coordinate of the intersection of the two symmetric tangent lines. -/
def polygonTangentialVertexCoordinate (θ d : ℝ) : ℝ :=
  Real.tanh d / Real.cos (polygonTangentialHalfAngle θ d)

theorem polygonTangentialVertexCoordinate_pos {θ d : ℝ}
    (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    0 < polygonTangentialVertexCoordinate θ d := by
  unfold polygonTangentialVertexCoordinate
  apply div_pos _ (polygonTangentialHalfAngle_cos_pos hθ hd)
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hd) (Real.cosh_pos d)

/-- The exact defect identity controlling finite versus ideal vertices. -/
theorem polygonTangentialVertexCoordinate_defect {θ d : ℝ}
    (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    (1-polygonTangentialVertexCoordinate θ d ^ 2) *
      (Real.cosh d * Real.cos (polygonTangentialHalfAngle θ d)) ^ 2 = Real.sin (θ/2)^2 := by
  have hc := (Real.cosh_pos d).ne'
  have hα := (polygonTangentialHalfAngle_cos_pos hθ hd).ne'
  have hs := polygonTangentialHalfAngle_sin (d := d) hθ
  have ht := Real.sin_sq_add_cos_sq (polygonTangentialHalfAngle θ d)
  have hθt := Real.sin_sq_add_cos_sq (θ/2)
  have hhyper := Real.cosh_sq_sub_sinh_sq d
  rw [hs] at ht
  unfold polygonTangentialVertexCoordinate
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp at ht ⊢
  nlinarith [sq_nonneg (Real.sinh d)]

theorem polygonTangentialVertexCoordinate_le_one {θ d : ℝ}
    (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    polygonTangentialVertexCoordinate θ d ≤ 1 := by
  have hdef := polygonTangentialVertexCoordinate_defect hθ hd
  have hp := polygonTangentialVertexCoordinate_pos hθ hd
  have hf : 0 < (Real.cosh d * Real.cos (polygonTangentialHalfAngle θ d))^2 :=
    sq_pos_of_pos (mul_pos (Real.cosh_pos d) (polygonTangentialHalfAngle_cos_pos hθ hd))
  have hs := sq_nonneg (Real.sin (θ/2))
  have hnon : 0 ≤ 1-polygonTangentialVertexCoordinate θ d ^ 2 :=
    nonneg_of_mul_nonneg_left (hdef.symm ▸ hs) hf
  nlinarith

theorem polygonTangentialVertexCoordinate_lt_one {θ d : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) (hd : 0 < d) :
    polygonTangentialVertexCoordinate θ d < 1 := by
  have hθ' : θ ∈ Ico (0 : ℝ) Real.pi := ⟨hθ.1.le,hθ.2⟩
  have hdef := polygonTangentialVertexCoordinate_defect hθ' hd
  have hp := polygonTangentialVertexCoordinate_pos hθ' hd
  have hf : 0 < (Real.cosh d * Real.cos (polygonTangentialHalfAngle θ d))^2 :=
    sq_pos_of_pos (mul_pos (Real.cosh_pos d) (polygonTangentialHalfAngle_cos_pos hθ' hd))
  have hs : 0 < Real.sin (θ/2)^2 := sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi
    (by linarith only [hθ.1]) (by linarith only [hθ.2,Real.pi_pos]))
  have hnon : 0 < 1-polygonTangentialVertexCoordinate θ d ^ 2 :=
    pos_of_mul_pos_left (hdef.symm ▸ hs) hf.le
  nlinarith

theorem polygonTangentialVertexCoordinate_eq_one_iff {θ d : ℝ}
    (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    polygonTangentialVertexCoordinate θ d = 1 ↔ θ = 0 := by
  constructor
  · intro he
    by_contra hne
    have hlt := polygonTangentialVertexCoordinate_lt_one ⟨lt_of_le_of_ne hθ.1 (Ne.symm hne),hθ.2⟩ hd
    exact hlt.ne he
  · rintro rfl
    have hdef := polygonTangentialVertexCoordinate_defect hθ hd
    have hp := polygonTangentialVertexCoordinate_pos hθ hd
    have hf : (Real.cosh d * Real.cos (polygonTangentialHalfAngle 0 d))^2 ≠ 0 :=
      pow_ne_zero 2 (mul_ne_zero (Real.cosh_pos d).ne' (polygonTangentialHalfAngle_cos_pos hθ hd).ne')
    norm_num only [zero_div,Real.sin_zero,zero_pow] at hdef
    have he := (mul_eq_zero.mp hdef).resolve_right hf
    nlinarith

/-- The actual closed Klein vertex; zero prescribed angle gives an actual ideal endpoint. -/
def polygonTangentialKleinVertex (θ d : ℝ) (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) : 𝕔𝔻 :=
  Complex.UnitClosedDisc.mk (polygonTangentialVertexCoordinate θ d : ℂ) (by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (polygonTangentialVertexCoordinate_pos hθ hd)]
    exact polygonTangentialVertexCoordinate_le_one hθ hd)

/-- Transport the constructed actual point to the native closed Poincare model. -/
def polygonTangentialDiscVertex (θ d : ℝ) (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) : 𝕔𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinHomeomorph.symm (polygonTangentialKleinVertex θ d hθ hd)

theorem polygonTangentialDiscVertex_coordinate (θ d : ℝ) (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (polygonTangentialDiscVertex θ d hθ hd) =
      (polygonTangentialVertexCoordinate θ d : ℂ) := by
  exact congrArg (fun p : 𝕔𝔻 => (p : ℂ))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinHomeomorph.apply_symm_apply
      (polygonTangentialKleinVertex θ d hθ hd))

/-- Ideal points are exactly preserved by the genuine closed Klein coordinate. -/
theorem norm_closedKleinCoordinate_eq_one_iff (p : 𝕔𝔻) :
    ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p‖ = 1 ↔ ‖(p : ℂ)‖ = 1 := by
  change ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula p‖ = 1 ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_norm]
  have hd : 0 < 1 + ‖(p : ℂ)‖^2 := by positivity
  rw [div_eq_one_iff_eq hd.ne']
  constructor <;> intro h <;> nlinarith

theorem polygonTangentialDiscVertex_ideal_iff (θ d : ℝ) (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    ‖(polygonTangentialDiscVertex θ d hθ hd : ℂ)‖ = 1 ↔ θ = 0 := by
  rw [← norm_closedKleinCoordinate_eq_one_iff,polygonTangentialDiscVertex_coordinate,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (polygonTangentialVertexCoordinate_pos hθ hd),
    polygonTangentialVertexCoordinate_eq_one_iff hθ hd]

/-- The two outward Euclidean unit normals of the genuine Klein tangent-line configuration. -/
def polygonTangentialNormal (θ d : ℝ) (ε : ℝ) : ℂ :=
  ⟨Real.cos (polygonTangentialHalfAngle θ d),ε*Real.sin (polygonTangentialHalfAngle θ d)⟩

theorem polygonTangentialNormal_norm (θ d ε : ℝ) (hε : ε^2 = 1) :
    ‖polygonTangentialNormal θ d ε‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [Complex.sq_norm]
  simp only [polygonTangentialNormal,Complex.normSq_mk]
  nlinarith only [Real.sin_sq_add_cos_sq (polygonTangentialHalfAngle θ d),
    congrArg (fun x : ℝ => x * Real.sin (polygonTangentialHalfAngle θ d)^2) hε]

theorem polygonTangentialVertex_on_tangent (θ d ε : ℝ)
    (hθ : θ ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) :
    inner ℝ (polygonTangentialNormal θ d ε)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (polygonTangentialDiscVertex θ d hθ hd)) = Real.tanh d := by
  rw [polygonTangentialDiscVertex_coordinate]
  simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,polygonTangentialNormal,Complex.ofReal_re,Complex.ofReal_im,mul_zero,add_zero]
  unfold polygonTangentialVertexCoordinate
  field_simp [(polygonTangentialHalfAngle_cos_pos hθ hd).ne']

end
end LowDimensionalTopology.Geometry.Polygon

@[expose] public section
open Set InnerProductGeometry
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section
-- BEGIN NEW TANGENTIAL CORNER BLOCK

theorem polygonTangential_tanh_pos {d : ℝ} (hd : 0 < d) : 0 < Real.tanh d := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hd) (Real.cosh_pos d)

theorem polygonTangential_tanh_mem {d : ℝ} (hd : 0 < d) : Real.tanh d ∈ Ioo (0 : ℝ) 1 :=
  ⟨polygonTangential_tanh_pos hd,Real.tanh_lt_one d⟩

/-- The two actual native tangent geodesics bounding a prescribed-angle corner. -/
def polygonTangentialSide (θ d ε : ℝ) (hd : 0 < d) (hε : ε^2 =
  1) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine (polygonTangentialNormal θ d ε) (Real.tanh d)
    (polygonTangentialNormal_norm θ d ε hε) (polygonTangential_tanh_mem hd)

theorem polygonTangentialSide_vertex (θ d ε : ℝ) (hθ : θ ∈ Ico (0 : ℝ) Real.pi)
    (hd : 0 < d) (hε : ε^2 = 1) :
    polygonTangentialDiscVertex θ d hθ hd ∈ (polygonTangentialSide θ d ε hd hε).closedCarrier := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_closed_equation_iff _ _ _ _ _).mpr
  exact polygonTangentialVertex_on_tangent θ d ε hθ hd

/-- The actual finite foot on each symmetric tangent side, constructed in the true Klein model. -/
def polygonTangentialFoot (θ d ε : ℝ) (hd : 0 < d) (hε : ε^2 = 1) : 𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph.symm (Complex.UnitDisc.mk (Real.tanh d • polygonTangentialNormal θ d ε) (by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (polygonTangential_tanh_pos hd),
      polygonTangentialNormal_norm θ d ε hε,mul_one]
    exact Real.tanh_lt_one d))

theorem polygonTangentialFoot_coordinate (θ d ε : ℝ) (hd : 0 < d) (hε : ε^2 = 1) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (polygonTangentialFoot θ d ε hd hε) = Real.tanh d • polygonTangentialNormal θ d ε := by
  exact congrArg (fun z : 𝔻 => (z :
    ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph.apply_symm_apply _)

theorem polygonTangentialFoot_mem_side (θ d ε : ℝ) (hd : 0 < d) (hε : ε^2 = 1) :
    polygonTangentialFoot θ d ε hd hε ∈ (polygonTangentialSide θ d ε hd hε).carrier := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_equation_iff _ _ _ _ _).mpr
  rw [polygonTangentialFoot_coordinate,real_inner_smul_right,real_inner_self_eq_norm_sq,
    polygonTangentialNormal_norm θ d ε hε,one_pow,mul_one]

/-- Lorentz-unit normal data for each actual tangent side. -/
theorem polygonTangentialSide_lorentz_unit (θ d ε : ℝ) (hε : ε^2 = 1) :
    ‖Real.cosh d • polygonTangentialNormal θ d ε‖^2 - Real.sinh d^2 = 1 := by
  rw [norm_smul,Real.norm_eq_abs,polygonTangentialNormal_norm θ d ε hε,mul_one,sq_abs]
  exact Real.cosh_sq_sub_sinh_sq d

theorem polygonTangentialSide_lorentz_equation (θ d ε : ℝ) (hd : 0 < d) (hε : ε^2 = 1)
    (z : 𝔻) (hz : z ∈ (polygonTangentialSide θ d ε hd hε).carrier) :
    inner ℝ (Real.cosh d • polygonTangentialNormal θ d ε) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = Real.sinh d := by
  have he := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_equation_iff _ _ _ _ z).mp hz
  rw [real_inner_smul_left,he,Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos d).ne']

/-- The actual adjacent tangent-side normal pairing recovers the prescribed corner angle. -/
theorem polygonTangentialSide_normal_pair {θ d : ℝ} (hθ : θ ∈ Ico (0 : ℝ) Real.pi) :
    inner ℝ (Real.cosh d • polygonTangentialNormal θ d 1)
      (Real.cosh d • polygonTangentialNormal θ d (-1)) - Real.sinh d^2 = -Real.cos θ := by
  rw [real_inner_smul_left,real_inner_smul_right,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  simp only [polygonTangentialNormal,one_mul,neg_one_mul]
  have hs := polygonTangentialHalfAngle_sin (d := d) hθ
  have ht := Real.sin_sq_add_cos_sq (polygonTangentialHalfAngle θ d)
  have hθc := Real.cos_two_mul (θ/2)
  have hhyper := Real.cosh_sq_sub_sinh_sq d
  have he : Real.cosh d * Real.sin (polygonTangentialHalfAngle θ d) = Real.cos (θ/2) := by
    rw [hs]
    field_simp [(Real.cosh_pos d).ne']
  have he2 := congrArg (fun x : ℝ => x^2) he
  have ht2 := congrArg (fun x : ℝ => Real.cosh d^2*x) ht
  rw [show 2*(θ/2)=θ by ring] at hθc
  nlinarith only [he2,ht2,hhyper,hθc]

end
end LowDimensionalTopology.Geometry.Polygon
