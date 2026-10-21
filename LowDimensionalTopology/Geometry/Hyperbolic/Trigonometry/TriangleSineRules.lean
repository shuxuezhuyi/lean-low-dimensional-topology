/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleCosineRule

@[expose] public section
open Set
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

def hyperbolicTriangleDiscriminant (a b c : ℝ) : ℝ :=
  1 + 2 * Real.cosh a * Real.cosh b * Real.cosh c -
    Real.cosh a ^ 2 - Real.cosh b ^ 2 - Real.cosh c ^ 2

theorem hyperbolic_sine_discriminant {a b c θ : ℝ}
    (hcos : Real.cosh a = Real.cosh b * Real.cosh c -
      Real.sinh b * Real.sinh c * Real.cos θ) :
    (Real.sinh b * Real.sinh c * Real.sin θ) ^ 2 = hyperbolicTriangleDiscriminant a b c := by
  have hp : Real.sinh b * Real.sinh c * Real.cos θ =
      Real.cosh b * Real.cosh c - Real.cosh a := by linarith only [hcos]
  have ht : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    linarith only [Real.sin_sq_add_cos_sq θ]
  calc
    _ = Real.sinh b ^ 2 * Real.sinh c ^ 2 -
        (Real.sinh b * Real.sinh c * Real.cos θ) ^ 2 := by
      rw [mul_pow,mul_pow,ht]
      ring
    _ = (Real.cosh b ^ 2 - 1) * (Real.cosh c ^ 2 - 1) -
        (Real.cosh b * Real.cosh c - Real.cosh a) ^ 2 := by
      rw [hp,Real.sinh_sq,Real.sinh_sq]
    _ = _ := by dsimp only [hyperbolicTriangleDiscriminant]; ring

theorem hyperbolic_sine_cross_eq {a b c θ η : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) (hη : η ∈ Ioo (0 : ℝ) Real.pi)
    (hcosθ : Real.cosh a = Real.cosh b * Real.cosh c -
      Real.sinh b * Real.sinh c * Real.cos θ)
    (hcosη : Real.cosh b = Real.cosh c * Real.cosh a -
      Real.sinh c * Real.sinh a * Real.cos η) :
    Real.sinh a * Real.sin η = Real.sinh b * Real.sin θ := by
  have hsina := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsinb := Real.sin_pos_of_pos_of_lt_pi hη.1 hη.2
  have hsa := Real.sinh_pos_iff.mpr ha
  have hsb := Real.sinh_pos_iff.mpr hb
  have hsc := Real.sinh_pos_iff.mpr hc
  have hd : hyperbolicTriangleDiscriminant a b c = hyperbolicTriangleDiscriminant b c a := by
    dsimp only [hyperbolicTriangleDiscriminant]
    ring
  have hsq := (hyperbolic_sine_discriminant hcosθ).trans
    (hd.trans (hyperbolic_sine_discriminant hcosη).symm)
  have he := (sq_eq_sq₀ (by positivity : 0 ≤ Real.sinh b * Real.sinh c * Real.sin θ)
    (by positivity : 0 ≤ Real.sinh c * Real.sinh a * Real.sin η)).mp hsq
  apply mul_left_cancel₀ (ne_of_gt hsc)
  calc
    _ = Real.sinh c * Real.sinh a * Real.sin η := by ring
    _ = Real.sinh b * Real.sinh c * Real.sin θ := he.symm
    _ = _ := by ring

/-- The sine rule with the actual three interior angles. -/
theorem HTriangle.sine_rule (T : HTriangle) :
    Real.sinh T.lengthA / Real.sin T.alpha = Real.sinh T.lengthB / Real.sin T.beta ∧
      Real.sinh T.lengthB / Real.sin T.beta = Real.sinh T.lengthC / Real.sin T.gamma := by
  have hα := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.1.1 T.angles_mem_Ioo.1.2
  have hβ := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.2.1.1 T.angles_mem_Ioo.2.1.2
  have hγ := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.2.2.1 T.angles_mem_Ioo.2.2.2
  constructor
  · apply (div_eq_div_iff (ne_of_gt hα) (ne_of_gt hβ)).mpr
    exact hyperbolic_sine_cross_eq T.lengths_pos.1 T.lengths_pos.2.1 T.lengths_pos.2.2
      T.angles_mem_Ioo.1 T.angles_mem_Ioo.2.1 T.cosine_rule_A T.cosine_rule_B
  · apply (div_eq_div_iff (ne_of_gt hβ) (ne_of_gt hγ)).mpr
    exact hyperbolic_sine_cross_eq T.lengths_pos.2.1 T.lengths_pos.2.2 T.lengths_pos.1
      T.angles_mem_Ioo.2.1 T.angles_mem_Ioo.2.2 T.cosine_rule_B T.cosine_rule_I

theorem DiscTriangle.sine_rule (T : DiscTriangle) :
    Real.sinh T.lengthA / Real.sin T.alpha = Real.sinh T.lengthB / Real.sin T.beta ∧
      Real.sinh T.lengthB / Real.sin T.beta = Real.sinh T.lengthC / Real.sin T.gamma := by
  rw [T.lengths_eq_halfPlane.1,T.lengths_eq_halfPlane.2.1,T.lengths_eq_halfPlane.2.2,
    T.angles_eq_halfPlane.1,T.angles_eq_halfPlane.2.1,T.angles_eq_halfPlane.2.2]
  exact T.toHalfPlane.sine_rule

theorem hyperbolic_second_cosine_rule {a b c α β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hα : α ∈ Ioo (0 : ℝ) Real.pi) (hβ : β ∈ Ioo (0 : ℝ) Real.pi)
    (hA : Real.cosh a = Real.cosh b * Real.cosh c -
      Real.sinh b * Real.sinh c * Real.cos α)
    (hB : Real.cosh b = Real.cosh c * Real.cosh a -
      Real.sinh c * Real.sinh a * Real.cos β)
    (hC : Real.cosh c = Real.cosh a * Real.cosh b -
      Real.sinh a * Real.sinh b * Real.cos γ) :
    Real.cosh c = (Real.cos α * Real.cos β + Real.cos γ) / (Real.sin α * Real.sin β) := by
  have hsinα := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hsinβ := Real.sin_pos_of_pos_of_lt_pi hβ.1 hβ.2
  have hsa := Real.sinh_pos_iff.mpr ha
  have hsb := Real.sinh_pos_iff.mpr hb
  have hsc := Real.sinh_pos_iff.mpr hc
  have hcross := hyperbolic_sine_cross_eq ha hb hc hα hβ hA hB
  have hdisc := hyperbolic_sine_discriminant hA
  have hA' : Real.sinh b * Real.sinh c * Real.cos α =
      Real.cosh b * Real.cosh c - Real.cosh a := by linarith only [hA]
  have hB' : Real.sinh c * Real.sinh a * Real.cos β =
      Real.cosh c * Real.cosh a - Real.cosh b := by linarith only [hB]
  have hC' : Real.sinh a * Real.sinh b * Real.cos γ =
      Real.cosh a * Real.cosh b - Real.cosh c := by linarith only [hC]
  have hscaled : (Real.sinh a * Real.sinh b * Real.sinh c ^ 2) *
      (Real.cos α * Real.cos β + Real.cos γ) = Real.cosh c * hyperbolicTriangleDiscriminant a b c := by
    calc
      _ = (Real.sinh b * Real.sinh c * Real.cos α) *
          (Real.sinh c * Real.sinh a * Real.cos β) +
          Real.sinh c ^ 2 * (Real.sinh a * Real.sinh b * Real.cos γ) := by ring
      _ = _ := by
        rw [hA',hB',hC',Real.sinh_sq]
        dsimp only [hyperbolicTriangleDiscriminant]
        ring
  have hnum : Real.cos α * Real.cos β + Real.cos γ = Real.cosh c * Real.sin α * Real.sin β := by
    apply mul_left_cancel₀ (by positivity : Real.sinh a * Real.sinh b * Real.sinh c ^ 2 ≠ 0)
    calc
      _ = Real.cosh c * hyperbolicTriangleDiscriminant a b c := hscaled
      _ = Real.cosh c * (Real.sinh b * Real.sinh c * Real.sin α) ^ 2 := by rw [hdisc]
      _ = Real.cosh c * Real.sinh b * Real.sinh c ^ 2 * Real.sin α *
          (Real.sinh a * Real.sin β) := by rw [hcross]; ring
      _ = _ := by ring
  apply (eq_div_iff (mul_ne_zero (ne_of_gt hsinα) (ne_of_gt hsinβ))).mpr
  simpa only [mul_assoc] using hnum.symm

/-- The second cosine rule for actual finite hyperbolic triangles. -/
theorem HTriangle.cosine_rule_II (T : HTriangle) :
    Real.cosh T.lengthC = (Real.cos T.alpha * Real.cos T.beta + Real.cos T.gamma) /
      (Real.sin T.alpha * Real.sin T.beta) :=
  hyperbolic_second_cosine_rule T.lengths_pos.1 T.lengths_pos.2.1 T.lengths_pos.2.2
    T.angles_mem_Ioo.1 T.angles_mem_Ioo.2.1 T.cosine_rule_A T.cosine_rule_B T.cosine_rule_I

theorem DiscTriangle.cosine_rule_II (T : DiscTriangle) :
    Real.cosh T.lengthC = (Real.cos T.alpha * Real.cos T.beta + Real.cos T.gamma) /
      (Real.sin T.alpha * Real.sin T.beta) := by
  rw [T.lengths_eq_halfPlane.2.2,T.angles_eq_halfPlane.1,T.angles_eq_halfPlane.2.1,
    T.angles_eq_halfPlane.2.2]
  exact T.toHalfPlane.cosine_rule_II

end
end LowDimensionalTopology.Geometry.Hyperbolic
