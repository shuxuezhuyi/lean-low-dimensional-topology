module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Pentagon.PentagonNormals
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- A genuine finite convex six-cycle of actual h-lines and six actual right angles.
The half-plane signs specify convex support positions; no metric formula is a field. -/
structure RightHexagon where
  vertex : Fin 6 → ℍ
  vertex_injective : Function.Injective vertex
  side : Fin 6 → _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine
  right_angle : ∀ i : Fin 6, (side i).OrthogonalAt (side (i + 1)) (vertex (i + 1))
  same_side : ∀ i j k : Fin 6, j ≠ i → j ≠ i + 1 → k ≠ i → k ≠ i + 1 →
    0 < (side i).normalTimeAt (vertex j) * (side i).normalTimeAt (vertex k)

def RightHexagon.edgeLength (Q : RightHexagon) (i : Fin 6) : ℝ := dist (Q.vertex i) (Q.vertex (i + 1))

def RightHexagon.sideA₁ (Q : RightHexagon) : ℝ := Q.edgeLength 0

def RightHexagon.sideA₂ (Q : RightHexagon) : ℝ := Q.edgeLength 4

def RightHexagon.sideA₃ (Q : RightHexagon) : ℝ := Q.edgeLength 2

def RightHexagon.sideB₁ (Q : RightHexagon) : ℝ := Q.edgeLength 3

def RightHexagon.sideB₂ (Q : RightHexagon) : ℝ := Q.edgeLength 1

def RightHexagon.sideB₃ (Q : RightHexagon) : ℝ := Q.edgeLength 5

theorem RightHexagon.edgeLength_pos (Q : RightHexagon) (i : Fin 6) : 0 < Q.edgeLength i := by
  apply dist_pos.mpr
  apply Q.vertex_injective.ne
  intro h
  simp at h

/-- The native right-hexagon cosine identity uses actual pairwise path distances. -/
theorem RightHexagon.cosh_sinh_sinh_identity (Q : RightHexagon) :
    Real.cosh Q.sideB₁ * Real.sinh Q.sideA₂ * Real.sinh Q.sideA₃ =
      Real.cosh Q.sideA₁ + Real.cosh Q.sideA₂ * Real.cosh Q.sideA₃ := by
  have ha : (Q.side 3).OrthogonalAt (Q.side 4) (Q.vertex 4) := Q.right_angle 3
  have hb : (Q.side 4).OrthogonalAt (Q.side 5) (Q.vertex 5) := Q.right_angle 4
  have he0 : (Q.side 2).OrthogonalAt (Q.side 3) (Q.vertex 3) := Q.right_angle 2
  have he : (Q.side 3).OrthogonalAt (Q.side 2) (Q.vertex 3) :=
    ⟨he0.2.1,he0.1,by rw [real_inner_comm]; exact he0.2.2⟩
  have hd0 : (Q.side 1).OrthogonalAt (Q.side 2) (Q.vertex 2) := Q.right_angle 1
  have hd : (Q.side 2).OrthogonalAt (Q.side 1) (Q.vertex 2) :=
    ⟨hd0.2.1,hd0.1,by rw [real_inner_comm]; exact hd0.2.2⟩
  have hu : (Q.side 5).OrthogonalAt (Q.side 0) (Q.vertex 0) := Q.right_angle 5
  have hv : (Q.side 0).OrthogonalAt (Q.side 1) (Q.vertex 1) := Q.right_angle 0
  have hchain := (Q.side 3).four_right_chain_inward_pairing (Q.side 4) (Q.side 2) (Q.side 5) (Q.side 1)
    (Q.vertex 4) (Q.vertex 5) (Q.vertex 3) (Q.vertex 2) ha hb he hd
    (Q.vertex_injective.ne (by decide : (4 : Fin 6) ≠ 5))
    (Q.vertex_injective.ne (by decide : (3 : Fin 6) ≠ 2))
    (Q.same_side 3 5 2 (by decide) (by decide) (by decide) (by decide))
  have hwidth := (Q.side 5).inward_pairing_two_right_angles (Q.side 0) (Q.side 1)
    (Q.vertex 0) (Q.vertex 1) hu hv (Q.vertex_injective.ne (by decide : (0 : Fin 6) ≠ 1))
  have hMsign := (Q.side 1).inwardNormalSign_eq_of_time_mul_pos (Q.vertex 0) (Q.vertex 3)
    (Q.same_side 1 0 3 (by decide) (by decide) (by decide) (by decide))
  have hLsign := (Q.side 5).inwardNormalSign_eq_of_time_mul_pos (Q.vertex 1) (Q.vertex 4)
    (Q.same_side 5 1 4 (by decide) (by decide) (by decide) (by decide))
  rw [hMsign,hLsign,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalPairing_comm] at hwidth
  rw [dist_comm (Q.vertex 3) (Q.vertex 2),dist_comm (Q.vertex 4) (Q.vertex 3)] at hchain
  change Real.cosh (Q.edgeLength 3) * Real.sinh (Q.edgeLength 4) * Real.sinh (Q.edgeLength 2) =
    Real.cosh (Q.edgeLength 0) + Real.cosh (Q.edgeLength 4) * Real.cosh (Q.edgeLength 2)
  change Real.cosh (dist (Q.vertex 3) (Q.vertex 4)) *
      Real.sinh (dist (Q.vertex 4) (Q.vertex 5)) * Real.sinh (dist (Q.vertex 2) (Q.vertex 3)) =
    Real.cosh (dist (Q.vertex 0) (Q.vertex 1)) +
      Real.cosh (dist (Q.vertex 4) (Q.vertex 5)) * Real.cosh (dist (Q.vertex 2) (Q.vertex 3))
  nlinarith only [hchain,hwidth]

/-- Cyclic relabeling preserves the actual vertices, sides, right angles and convex side positions. -/
def RightHexagon.rotate (Q : RightHexagon) (t : Fin 6) : RightHexagon where
  vertex i := Q.vertex (i + t)
  vertex_injective := fun _ _ he => add_right_cancel (Q.vertex_injective he)
  side i := Q.side (i + t)
  right_angle i := by
    have hi : (i + 1) + t = (i + t) + 1 := by abel
    change (Q.side (i + t)).OrthogonalAt (Q.side ((i + 1) + t)) (Q.vertex ((i + 1) + t))
    rw [hi]
    exact Q.right_angle (i + t)
  same_side i j k hj hjs hk hks := by
    apply Q.same_side (i + t) (j + t) (k + t)
    · exact fun he => hj (add_right_cancel he)
    · intro he
      apply hjs
      apply add_right_cancel
      calc
        j + t = (i + t) + 1 := he
        _ = (i + 1) + t := by abel
    · exact fun he => hk (add_right_cancel he)
    · intro he
      apply hks
      apply add_right_cancel
      calc
        k + t = (i + t) + 1 := he
        _ = (i + 1) + t := by abel

theorem RightHexagon.rotate_edgeLength (Q : RightHexagon) (t i : Fin 6) :
    (Q.rotate t).edgeLength i = Q.edgeLength (i + t) := by
  change dist (Q.vertex (i + t)) (Q.vertex ((i + 1) + t)) =
    dist (Q.vertex (i + t)) (Q.vertex ((i + t) + 1))
  rw [show (i + 1) + t = (i + t) + 1 by abel]

/-- All three cyclic instances of the actual right-hexagon cosine law. -/
theorem RightHexagon.cosine_rules_cyclic (Q : RightHexagon) :
    Real.cosh Q.sideB₁ * Real.sinh Q.sideA₂ * Real.sinh Q.sideA₃ =
      Real.cosh Q.sideA₁ + Real.cosh Q.sideA₂ * Real.cosh Q.sideA₃ ∧
    Real.cosh Q.sideB₂ * Real.sinh Q.sideA₁ * Real.sinh Q.sideA₃ =
      Real.cosh Q.sideA₂ + Real.cosh Q.sideA₁ * Real.cosh Q.sideA₃ ∧
    Real.cosh Q.sideB₃ * Real.sinh Q.sideA₁ * Real.sinh Q.sideA₂ =
      Real.cosh Q.sideA₃ + Real.cosh Q.sideA₁ * Real.cosh Q.sideA₂ := by
  have h₂ := (Q.rotate 4).cosh_sinh_sinh_identity
  have h₃ := (Q.rotate 2).cosh_sinh_sinh_identity
  simp only [RightHexagon.sideA₁,RightHexagon.sideA₂,RightHexagon.sideA₃,RightHexagon.sideB₁,RightHexagon.rotate_edgeLength] at h₂ h₃
  refine ⟨Q.cosh_sinh_sinh_identity,?_,?_⟩
  · change Real.cosh (Q.edgeLength 1) * Real.sinh (Q.edgeLength 2) * Real.sinh (Q.edgeLength 0) =
      Real.cosh (Q.edgeLength 4) + Real.cosh (Q.edgeLength 2) * Real.cosh (Q.edgeLength 0) at h₂
    change Real.cosh (Q.edgeLength 1) * Real.sinh (Q.edgeLength 0) * Real.sinh (Q.edgeLength 2) =
      Real.cosh (Q.edgeLength 4) + Real.cosh (Q.edgeLength 0) * Real.cosh (Q.edgeLength 2)
    nlinarith only [h₂]
  · change Real.cosh (Q.edgeLength 5) * Real.sinh (Q.edgeLength 0) * Real.sinh (Q.edgeLength 4) =
      Real.cosh (Q.edgeLength 2) + Real.cosh (Q.edgeLength 0) * Real.cosh (Q.edgeLength 4) at h₃
    exact h₃

/-- The common algebraic discriminant in the three exact hexagon cosine laws. -/
def hexagonCosineDiscriminant (a b c : ℝ) : ℝ :=
  Real.cosh a ^ 2 + Real.cosh b ^ 2 + Real.cosh c ^ 2 +
    2 * Real.cosh a * Real.cosh b * Real.cosh c - 1

theorem hexagon_sinh_discriminant (a b c u : ℝ)
    (hu : Real.cosh u * Real.sinh b * Real.sinh c = Real.cosh a + Real.cosh b * Real.cosh c) :
    Real.sinh u ^ 2 * Real.sinh b ^ 2 * Real.sinh c ^ 2 = hexagonCosineDiscriminant a b c := by
  have hu' : Real.sinh u ^ 2 = Real.cosh u ^ 2 - 1 := by
    linarith only [Real.cosh_sq_sub_sinh_sq u]
  have hb' : Real.sinh b ^ 2 = Real.cosh b ^ 2 - 1 := by
    linarith only [Real.cosh_sq_sub_sinh_sq b]
  have hc' : Real.sinh c ^ 2 = Real.cosh c ^ 2 - 1 := by
    linarith only [Real.cosh_sq_sub_sinh_sq c]
  calc
    _ = (Real.cosh u * Real.sinh b * Real.sinh c) ^ 2 - Real.sinh b ^ 2 * Real.sinh c ^ 2 := by
      rw [hu']
      ring
    _ = (Real.cosh a + Real.cosh b * Real.cosh c) ^ 2 - Real.sinh b ^ 2 * Real.sinh c ^ 2 := by rw [hu]
    _ = _ := by rw [hb',hc']; dsimp only [hexagonCosineDiscriminant]; ring

theorem hyperbolic_hexagon_sine_ratios (a b c u v w : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (h₁ : Real.cosh u * Real.sinh b * Real.sinh c = Real.cosh a + Real.cosh b * Real.cosh c)
    (h₂ : Real.cosh v * Real.sinh a * Real.sinh c = Real.cosh b + Real.cosh a * Real.cosh c)
    (h₃ : Real.cosh w * Real.sinh a * Real.sinh b = Real.cosh c + Real.cosh a * Real.cosh b) :
    Real.sinh a / Real.sinh u = Real.sinh b / Real.sinh v ∧
      Real.sinh b / Real.sinh v = Real.sinh c / Real.sinh w := by
  have hsa := Real.sinh_pos_iff.mpr ha
  have hsb := Real.sinh_pos_iff.mpr hb
  have hsc := Real.sinh_pos_iff.mpr hc
  have hsu := Real.sinh_pos_iff.mpr hu
  have hsv := Real.sinh_pos_iff.mpr hv
  have hsw := Real.sinh_pos_iff.mpr hw
  have hD₁ := hexagon_sinh_discriminant a b c u h₁
  have hD₂ := hexagon_sinh_discriminant b a c v h₂
  have hD₃ := hexagon_sinh_discriminant c a b w h₃
  have hD₂' : Real.sinh v ^ 2 * Real.sinh a ^ 2 * Real.sinh c ^ 2 = hexagonCosineDiscriminant a b c := by
    rw [hD₂]
    dsimp only [hexagonCosineDiscriminant]
    ring
  have hD₃' : Real.sinh w ^ 2 * Real.sinh a ^ 2 * Real.sinh b ^ 2 = hexagonCosineDiscriminant a b c := by
    rw [hD₃]
    dsimp only [hexagonCosineDiscriminant]
    ring
  have hcross₁sq : (Real.sinh u * Real.sinh b) ^ 2 = (Real.sinh v * Real.sinh a) ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hsc.ne')
    nlinarith only [hD₁,hD₂']
  have hcross₂sq : (Real.sinh v * Real.sinh c) ^ 2 = (Real.sinh w * Real.sinh b) ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hsa.ne')
    nlinarith only [hD₂',hD₃']
  have hcross₁ := (sq_eq_sq₀ (mul_pos hsu hsb).le (mul_pos hsv hsa).le).mp hcross₁sq
  have hcross₂ := (sq_eq_sq₀ (mul_pos hsv hsc).le (mul_pos hsw hsb).le).mp hcross₂sq
  constructor
  · apply (div_eq_div_iff hsu.ne' hsv.ne').mpr
    nlinarith only [hcross₁]
  · apply (div_eq_div_iff hsv.ne' hsw.ne').mpr
    nlinarith only [hcross₂]

/-- With all six true native side lengths. -/
theorem RightHexagon.sinh_opposite_side_ratios_eq (Q : RightHexagon) :
    Real.sinh Q.sideA₁ / Real.sinh Q.sideB₁ = Real.sinh Q.sideA₂ / Real.sinh Q.sideB₂ ∧
      Real.sinh Q.sideA₂ / Real.sinh Q.sideB₂ = Real.sinh Q.sideA₃ / Real.sinh Q.sideB₃ := by
  have hcos := Q.cosine_rules_cyclic
  exact hyperbolic_hexagon_sine_ratios _ _ _ _ _ _
    (Q.edgeLength_pos 0) (Q.edgeLength_pos 4) (Q.edgeLength_pos 2)
    (Q.edgeLength_pos 3) (Q.edgeLength_pos 1) (Q.edgeLength_pos 5) hcos.1 hcos.2.1 hcos.2.2

/-- The three true alternating side lengths determine the other three lengths. -/
theorem RightHexagon.remaining_sides_eq_of_alternating_eq (Q R : RightHexagon)
    (h₁ : Q.sideA₁ = R.sideA₁) (h₂ : Q.sideA₂ = R.sideA₂) (h₃ : Q.sideA₃ = R.sideA₃) :
    Q.sideB₁ = R.sideB₁ ∧ Q.sideB₂ = R.sideB₂ ∧ Q.sideB₃ = R.sideB₃ := by
  have hQ := Q.cosine_rules_cyclic
  have hR := R.cosine_rules_cyclic
  rw [← h₁,← h₂,← h₃] at hR
  have hsa₁ : Real.sinh Q.sideA₁ ≠ 0 := (Real.sinh_pos_iff.mpr (Q.edgeLength_pos 0)).ne'
  have hsa₂ : Real.sinh Q.sideA₂ ≠ 0 := (Real.sinh_pos_iff.mpr (Q.edgeLength_pos 4)).ne'
  have hsa₃ : Real.sinh Q.sideA₃ ≠ 0 := (Real.sinh_pos_iff.mpr (Q.edgeLength_pos 2)).ne'
  have hb₁ : Real.cosh Q.sideB₁ = Real.cosh R.sideB₁ := by
    apply mul_right_cancel₀ (mul_ne_zero hsa₂ hsa₃)
    nlinarith only [hQ.1,hR.1]
  have hb₂ : Real.cosh Q.sideB₂ = Real.cosh R.sideB₂ := by
    apply mul_right_cancel₀ (mul_ne_zero hsa₁ hsa₃)
    nlinarith only [hQ.2.1,hR.2.1]
  have hb₃ : Real.cosh Q.sideB₃ = Real.cosh R.sideB₃ := by
    apply mul_right_cancel₀ (mul_ne_zero hsa₁ hsa₂)
    nlinarith only [hQ.2.2,hR.2.2]
  exact ⟨Real.cosh_strictMonoOn.injOn (Q.edgeLength_pos 3).le (R.edgeLength_pos 3).le hb₁,
    Real.cosh_strictMonoOn.injOn (Q.edgeLength_pos 1).le (R.edgeLength_pos 1).le hb₂,
    Real.cosh_strictMonoOn.injOn (Q.edgeLength_pos 5).le (R.edgeLength_pos 5).le hb₃⟩

end
end LowDimensionalTopology.Geometry.Polygon
