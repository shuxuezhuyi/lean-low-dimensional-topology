module
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleInradius
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TwoIdealTriangles
@[expose] public section
open Set
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem cosine_eq_half_tangent_fraction (a : ℝ) (ha : a ∈ Ico (0 : ℝ) Real.pi) :
    Real.cos a = (1 - Real.tan (a / 2) ^ 2) / (1 + Real.tan (a / 2) ^ 2) := by
  have hc : 0 < Real.cos (a / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,ha.1],by linarith [ha.2]⟩
  apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1 + Real.tan (a / 2) ^ 2))).mpr
  rw [Real.tan_eq_sin_div_cos]
  have ht := Real.sin_sq_add_cos_sq (a / 2)
  have hd := Real.cos_two_mul (a / 2)
  rw [show 2 * (a / 2) = a by ring] at hd
  field_simp
  nlinarith only [ht,hd,congrArg (fun x : ℝ => Real.cos a * x) ht]

theorem half_tangent_pair_sum_lt_one (a b c : ℝ)
    (ha : a ∈ Ico (0 : ℝ) Real.pi) (hb : b ∈ Ico (0 : ℝ) Real.pi)
    (hc : c ∈ Ico (0 : ℝ) Real.pi) (hs : a + b + c < Real.pi) :
    Real.tan (a / 2) * Real.tan (b / 2) + Real.tan (a / 2) * Real.tan (c / 2) +
      Real.tan (b / 2) * Real.tan (c / 2) < 1 := by
  have hca : 0 < Real.cos (a / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,ha.1],by linarith [ha.2]⟩
  have hcb : 0 < Real.cos (b / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hb.1],by linarith [hb.2]⟩
  have hcc : 0 < Real.cos (c / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hc.1],by linarith [hc.2]⟩
  have hcs : 0 < Real.cos (a / 2 + b / 2 + c / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ha.1,hb.1,hc.1,Real.pi_pos],by linarith [hs]⟩
  have he : Real.cos (a / 2 + b / 2 + c / 2) =
      Real.cos (a / 2) * Real.cos (b / 2) * Real.cos (c / 2) *
        (1 - (Real.tan (a / 2) * Real.tan (b / 2) + Real.tan (a / 2) * Real.tan (c / 2) +
          Real.tan (b / 2) * Real.tan (c / 2))) := by
    rw [Real.cos_add,Real.cos_add,Real.sin_add,Real.tan_eq_sin_div_cos,
      Real.tan_eq_sin_div_cos,Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have hp : 0 < Real.cos (a / 2) * Real.cos (b / 2) * Real.cos (c / 2) := by positivity
  rw [he] at hcs
  nlinarith only [hp,hcs]

theorem inradius_half_tangent_polynomial_nonneg (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hq : x * y + x * z + y * z ≤ 1) :
    0 ≤ (x * y - x * z - y * z - 1) * (x * y - x * z + y * z + 1) *
      (x * y + x * z - y * z + 1) * (x * y + x * z + y * z - 1) -
      (1 - x * y - x * z - y * z) ^ 2 := by
  let p := x + y + z
  let q := x * y + x * z + y * z
  let r := x * y * z
  have hp : 0 ≤ p * (q + 1) - 2 * r := calc
    _ = x ^ 2 * y + x ^ 2 * z + x * y ^ 2 + x * z ^ 2 + y ^ 2 * z + y * z ^ 2 +
        x * y * z + x + y + z := by dsimp [p,q,r]; ring
    _ ≥ 0 := by positivity
  have hn : 0 ≤ (1 - q) * (q * (1 - q) * (q + 2) + 4 * r * (p * (q + 1) - 2 * r)) := by
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hr0 : 0 ≤ r := by dsimp [r]; positivity
    have hq1 : 0 ≤ 1 - q := by dsimp [q]; linarith
    positivity
  convert hn using 1
  dsimp [p,q,r]
  ring


theorem cosine_sum_tangent_expression (a b c : ℝ)
    (ha : Real.cos a ≠ 0) (hb : Real.cos b ≠ 0) (hc : Real.cos c ≠ 0) :
    Real.cos (a + b + c) = Real.cos a * Real.cos b * Real.cos c *
      (1 - Real.tan a * Real.tan b - Real.tan a * Real.tan c - Real.tan b * Real.tan c) := by
  rw [Real.cos_add,Real.cos_add,Real.sin_add,Real.tan_eq_sin_div_cos,
    Real.tan_eq_sin_div_cos,Real.tan_eq_sin_div_cos]
  field_simp
  ring

theorem cosine_tangent_unit (a : ℝ) (ha : Real.cos a ≠ 0) :
    Real.cos a ^ 2 * (1 + Real.tan a ^ 2) = 1 := by
  rw [Real.tan_eq_sin_div_cos,div_pow]
  field_simp
  nlinarith only [Real.sin_sq_add_cos_sq a]

theorem cosine_sum_tangent_sq (a b c : ℝ)
    (ha : Real.cos a ≠ 0) (hb : Real.cos b ≠ 0) (hc : Real.cos c ≠ 0) :
    Real.cos (a + b + c) ^ 2 =
      (1 - Real.tan a * Real.tan b - Real.tan a * Real.tan c - Real.tan b * Real.tan c) ^ 2 /
        ((1 + Real.tan a ^ 2) * (1 + Real.tan b ^ 2) * (1 + Real.tan c ^ 2)) := by
  have hd : (1 + Real.tan a ^ 2) * (1 + Real.tan b ^ 2) * (1 + Real.tan c ^ 2) ≠ 0 :=
    ne_of_gt (by positivity)
  apply (eq_div_iff hd).mpr
  rw [cosine_sum_tangent_expression a b c ha hb hc]
  have hp : (Real.cos a * Real.cos b * Real.cos c) ^ 2 *
      ((1 + Real.tan a ^ 2) * (1 + Real.tan b ^ 2) * (1 + Real.tan c ^ 2)) = 1 := by
    calc
      _ = (Real.cos a ^ 2 * (1 + Real.tan a ^ 2)) *
        (Real.cos b ^ 2 * (1 + Real.tan b ^ 2)) *
        (Real.cos c ^ 2 * (1 + Real.tan c ^ 2)) := by ring
      _ = _ := by rw [cosine_tangent_unit a ha,cosine_tangent_unit b hb,cosine_tangent_unit c hc]; ring
  calc
    _ = ((Real.cos a * Real.cos b * Real.cos c) ^ 2 *
        ((1 + Real.tan a ^ 2) * (1 + Real.tan b ^ 2) * (1 + Real.tan c ^ 2))) *
      (1 - Real.tan a * Real.tan b - Real.tan a * Real.tan c - Real.tan b * Real.tan c) ^ 2 := by ring
    _ = _ := by rw [hp,one_mul]

theorem half_tangent_radius_expression (x y z : ℝ) :
    let a := (1 - x ^ 2) / (1 + x ^ 2)
    let b := (1 - y ^ 2) / (1 + y ^ 2)
    let c := (1 - z ^ 2) / (1 + z ^ 2)
    4 * ((a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c - 1) /
      (2 * (1 + a) * (1 + b) * (1 + c))) =
      (x * y - x * z - y * z - 1) * (x * y - x * z + y * z + 1) *
        (x * y + x * z - y * z + 1) * (x * y + x * z + y * z - 1) /
        ((1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2)) := by
  dsimp only
  have hx : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hy : 1 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hz : 1 + z ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring


theorem inradius_angle_defect_squared_bound (a b c R : ℝ)
    (ha : a ∈ Ico (0 : ℝ) Real.pi) (hb : b ∈ Ico (0 : ℝ) Real.pi)
    (hc : c ∈ Ico (0 : ℝ) Real.pi) (hs : a + b + c < Real.pi)
    (hR : Real.tanh R ^ 2 = (Real.cos a ^ 2 + Real.cos b ^ 2 + Real.cos c ^ 2 +
      2 * Real.cos a * Real.cos b * Real.cos c - 1) /
      (2 * (1 + Real.cos a) * (1 + Real.cos b) * (1 + Real.cos c))) :
    Real.cos ((a + b + c) / 2) ^ 2 ≤ 4 * Real.tanh R ^ 2 := by
  let x := Real.tan (a / 2)
  let y := Real.tan (b / 2)
  let z := Real.tan (c / 2)
  have hx : 0 ≤ x := Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith [ha.1]) (by linarith [ha.2])
  have hy : 0 ≤ y := Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith [hb.1]) (by linarith [hb.2])
  have hz : 0 ≤ z := Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith [hc.1]) (by linarith [hc.2])
  have hq : x * y + x * z + y * z ≤ 1 := (half_tangent_pair_sum_lt_one a b c ha hb hc hs).le
  have hca : 0 < Real.cos (a / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,ha.1],by linarith [ha.2]⟩
  have hcb : 0 < Real.cos (b / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hb.1],by linarith [hb.2]⟩
  have hcc : 0 < Real.cos (c / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hc.1],by linarith [hc.2]⟩
  have hrad : 4 * Real.tanh R ^ 2 =
      (x * y - x * z - y * z - 1) * (x * y - x * z + y * z + 1) *
        (x * y + x * z - y * z + 1) * (x * y + x * z + y * z - 1) /
        ((1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2)) := by
    rw [hR,cosine_eq_half_tangent_fraction a ha,cosine_eq_half_tangent_fraction b hb,
      cosine_eq_half_tangent_fraction c hc]
    exact half_tangent_radius_expression x y z
  have hcos := cosine_sum_tangent_sq (a / 2) (b / 2) (c / 2) hca.ne' hcb.ne' hcc.ne'
  rw [show a / 2 + b / 2 + c / 2 = (a + b + c) / 2 by ring] at hcos
  rw [hrad,hcos]
  have hpoly := inradius_half_tangent_polynomial_nonneg x y z hx hy hz hq
  exact div_le_div_of_nonneg_right (sub_nonneg.mp hpoly) (by positivity)

theorem ClosedDiscTriangle.inradius_angle_defect_bound (T : ClosedDiscTriangle) :
    (1 / 2 : ℝ) * Real.sin ((Real.pi - T.alpha - T.beta - T.gamma) / 2) ≤ Real.tanh T.inradius := by
  have he := inradius_angle_defect_squared_bound T.alpha T.beta T.gamma T.inradius
    T.alpha_mem_Ico T.cycle.alpha_mem_Ico T.cycle.cycle.alpha_mem_Ico T.angle_sum_lt_pi T.tanh_inradius_sq_cosine_formula
  have htrig : Real.sin ((Real.pi - T.alpha - T.beta - T.gamma) / 2) =
      Real.cos ((T.alpha + T.beta + T.gamma) / 2) := by
    rw [show (Real.pi - T.alpha - T.beta - T.gamma) / 2 =
      Real.pi / 2 - (T.alpha + T.beta + T.gamma) / 2 by ring,Real.sin_pi_div_two_sub]
  have hr : 0 < Real.tanh T.inradius := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr T.inradius_pos) (Real.cosh_pos _)
  have hβ : 0 ≤ T.beta := T.cycle.alpha_mem_Ico.1
  have hγ : 0 ≤ T.gamma := T.cycle.cycle.alpha_mem_Ico.1
  have hs : 0 < Real.cos ((T.alpha + T.beta + T.gamma) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [T.alpha_mem_Ico.1,Real.pi_pos],by linarith [T.angle_sum_lt_pi]⟩
  rw [htrig]
  nlinarith only [he,hr,hs]

theorem ClosedDiscTriangle.two_ideal_inradius_formula (T : ClosedDiscTriangle)
    (hb : ‖(T.b : ℂ)‖ = 1) (hc : ‖(T.c : ℂ)‖ = 1) :
    4 * Real.tanh T.inradius ^ 2 = (1 + Real.cos T.alpha) / 2 ∧
      4 * Real.tanh T.inradius ^ 2 = Real.cos (T.alpha / 2) ^ 2 := by
  have hl := Real.cos_lt_cos_of_nonneg_of_le_pi T.alpha_mem_Ico.1 (le_refl Real.pi) T.alpha_mem_Ico.2
  rw [Real.cos_pi] at hl
  have hn : 1 + Real.cos T.alpha ≠ 0 := ne_of_gt (by linarith)
  have he := T.tanh_inradius_sq_cosine_formula
  rw [T.beta_of_ideal hb,T.gamma_of_ideal hc,Real.cos_zero] at he
  have hraw : Real.tanh T.inradius ^ 2 * (8 * (1 + Real.cos T.alpha)) =
      (1 + Real.cos T.alpha) ^ 2 := by
    field_simp at he
    nlinarith only [he]
  have hfirst : 4 * Real.tanh T.inradius ^ 2 = (1 + Real.cos T.alpha) / 2 := by
    apply mul_right_cancel₀ hn
    nlinarith only [hraw]
  refine ⟨hfirst,?_⟩
  have hd := Real.cos_two_mul (T.alpha / 2)
  rw [show 2 * (T.alpha / 2) = T.alpha by ring] at hd
  nlinarith only [hfirst,hd]

theorem ClosedDiscTriangle.two_ideal_inradius_area (T : ClosedDiscTriangle)
    (hb : ‖(T.b : ℂ)‖ = 1) (hc : ‖(T.c : ℂ)‖ = 1) :
    4 * Real.tanh T.inradius ^ 2 =
      Real.sin ((discHyperbolicArea T.interior).toReal / 2) ^ 2 := by
  have he := T.area_eq_angle_defect_of_exists_ideal (Or.inr (Or.inl hb))
  rw [T.beta_of_ideal hb,T.gamma_of_ideal hc,sub_zero,sub_zero] at he
  rw [he,ENNReal.toReal_ofReal (by linarith [T.alpha_mem_Ico.2] : 0 ≤ Real.pi - T.alpha),
    show (Real.pi - T.alpha) / 2 = Real.pi / 2 - T.alpha / 2 by ring,Real.sin_pi_div_two_sub]
  exact (T.two_ideal_inradius_formula hb hc).2


theorem ClosedDiscTriangle.inradius_area_bound (T : ClosedDiscTriangle) :
    (1 / 2 : ℝ) * Real.sin ((discHyperbolicArea T.interior).toReal / 2) ≤ Real.tanh T.inradius := by
  rw [T.area_toReal_eq_angle_defect]
  exact T.inradius_angle_defect_bound

/-- With actual native angles, distance inradius and area. -/
theorem exists_two_ideal_triangle_with_angle_area_inradius_identities (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    ∃ T : ClosedDiscTriangle, T.alpha = α ∧ T.beta = 0 ∧ T.gamma = 0 ∧
      4 * Real.tanh T.inradius ^ 2 = (1 + Real.cos α) / 2 ∧
      4 * Real.tanh T.inradius ^ 2 = Real.cos (α / 2) ^ 2 ∧
      4 * Real.tanh T.inradius ^ 2 = Real.sin ((discHyperbolicArea T.interior).toReal / 2) ^ 2 := by
  obtain ⟨T,hTa,hb,hc⟩ := exists_two_ideal_triangle_with_angle α hα
  have he := T.two_ideal_inradius_formula hb hc
  rw [hTa] at he
  exact ⟨T,hTa,T.beta_of_ideal hb,T.gamma_of_ideal hc,he.1,he.2,T.two_ideal_inradius_area hb hc⟩

/-- Every possible positive triangle area, including the ideal endpoint π, attains the bound. -/
theorem exists_inradius_area_equality (A : ℝ) (hA : A ∈ Ioc (0 : ℝ) Real.pi) :
    ∃ T : ClosedDiscTriangle, discHyperbolicArea T.interior = ENNReal.ofReal A ∧
      Real.tanh T.inradius = (1 / 2 : ℝ) * Real.sin (A / 2) := by
  obtain ⟨T,hTa,hb,hc⟩ := exists_two_ideal_triangle_with_angle_nonneg (Real.pi - A)
    ⟨by linarith [hA.2],by linarith [hA.1]⟩
  have harea : discHyperbolicArea T.interior = ENNReal.ofReal A := by
    rw [T.area_eq_angle_defect,hTa,T.beta_of_ideal hb,T.gamma_of_ideal hc,sub_zero,sub_zero]
    congr 1
    ring
  refine ⟨T,harea,?_⟩
  have he := T.two_ideal_inradius_area hb hc
  rw [harea,ENNReal.toReal_ofReal hA.1.le] at he
  have hr : 0 < Real.tanh T.inradius := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr T.inradius_pos) (Real.cosh_pos _)
  have hs : 0 < Real.sin (A / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hA.1])
    (by linarith [hA.2,Real.pi_pos])
  nlinarith only [he,hr,hs]

/-- The source lower bound uses the actual weighted-area measure and true metric inradius. -/
theorem ClosedDiscTriangle.half_sine_half_area_le_tanh_inradius (T : ClosedDiscTriangle) :
    (1 / 2 : ℝ) * Real.sin ((discHyperbolicArea T.interior).toReal / 2) ≤ Real.tanh T.inradius :=
  T.inradius_area_bound

end
end LowDimensionalTopology.Geometry.Hyperbolic
