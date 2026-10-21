/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleSineRules
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleIncenter
@[expose] public section
noncomputable section
open Set InnerProductGeometry
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic

/-- The actual positive invariant of three noncollinear interior vertices. -/
def halfTurnTriangleInvariant (T : HTriangle) : ℝ :=
  Real.sinh T.lengthB*Real.sinh T.lengthC*Real.sin T.alpha

theorem halfTurnTriangleInvariant_pos (T : HTriangle) : 0<halfTurnTriangleInvariant T := by
  exact mul_pos (mul_pos (Real.sinh_pos_iff.mpr T.lengths_pos.2.1)
    (Real.sinh_pos_iff.mpr T.lengths_pos.2.2))
    (Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.1.1 T.angles_mem_Ioo.1.2)

theorem halfTurnTriangleInvariant_eq_beta (T : HTriangle) :
    halfTurnTriangleInvariant T=Real.sinh T.lengthC*Real.sinh T.lengthA*Real.sin T.beta := by
  have he:=hyperbolic_sine_cross_eq T.lengths_pos.1 T.lengths_pos.2.1 T.lengths_pos.2.2
    T.angles_mem_Ioo.1 T.angles_mem_Ioo.2.1 T.cosine_rule_A T.cosine_rule_B
  dsimp only [halfTurnTriangleInvariant]
  linear_combination -(Real.sinh T.lengthC)*he

theorem halfTurnTriangleInvariant_eq_gamma (T : HTriangle) :
    halfTurnTriangleInvariant T=Real.sinh T.lengthA*Real.sinh T.lengthB*Real.sin T.gamma := by
  have he:=hyperbolic_sine_cross_eq T.lengths_pos.2.2 T.lengths_pos.1 T.lengths_pos.2.1
    T.angles_mem_Ioo.2.2 T.angles_mem_Ioo.1 T.cosine_rule_I T.cosine_rule_A
  dsimp only [halfTurnTriangleInvariant]
  linear_combination (Real.sinh T.lengthB)*he

/-- Its square is the actual side-length discriminant, with no angle or model hypothesis. -/
theorem halfTurnTriangleInvariant_sq (T : HTriangle) :
    (halfTurnTriangleInvariant T)^2=
      hyperbolicTriangleDiscriminant T.lengthA T.lengthB T.lengthC :=
  hyperbolic_sine_discriminant T.cosine_rule_A

theorem triangle_sinh_height_C (T : HTriangle) :
    Real.sinh (T.sideLineC.pointDist T.c)=Real.sin T.alpha*Real.sinh T.lengthB := by
  have he:=T.rayAB.sinh_pointDist_direction T.b_mem_rayAB T.a_ne_b.symm T.c T.c_ne_a
  have ha:=hInteriorAngleMeasure_eq_direction T.rayAB T.rayAC T.b_mem_rayAB T.a_ne_b.symm
    T.c_mem_rayAC T.c_ne_a
  change T.alpha=_ at ha
  change Real.sinh (T.sideLineC.pointDist T.c)=_ at he
  rw [←ha,dist_comm T.a T.c] at he
  exact he

theorem triangle_sinh_height_A (T : HTriangle) :
    Real.sinh (T.sideLineA.pointDist T.a)=Real.sin T.beta*Real.sinh T.lengthC := by
  have he:=T.rayBC.sinh_pointDist_direction T.c_mem_rayBC T.b_ne_c.symm T.a T.a_ne_b
  have ha:=hInteriorAngleMeasure_eq_direction T.rayBA T.rayBC T.a_mem_rayBA T.a_ne_b
    T.c_mem_rayBC T.b_ne_c.symm
  change T.beta=_ at ha
  change Real.sinh (T.sideLineA.pointDist T.a)=_ at he
  rw [angle_comm (hyperbolicDirection T.b T.c),←ha,dist_comm T.b T.a] at he
  exact he

theorem triangle_sinh_height_B (T : HTriangle) :
    Real.sinh (T.sideLineB.pointDist T.b)=Real.sin T.gamma*Real.sinh T.lengthA := by
  have he:=T.rayCA.sinh_pointDist_direction T.a_mem_rayCA T.c_ne_a.symm T.b T.b_ne_c
  have ha:=hInteriorAngleMeasure_eq_direction T.rayCA T.rayCB T.a_mem_rayCA T.c_ne_a.symm
    T.b_mem_rayCB T.b_ne_c
  change T.gamma=_ at ha
  change Real.sinh (T.sideLineB.pointDist T.b)=_ at he
  rw [←ha,dist_comm T.c T.b] at he
  exact he

/-- Any of the three genuine sides can be the base; the height is the true complete-line distance. -/
theorem halfTurnTriangleInvariant_base_heights (T : HTriangle) :
    halfTurnTriangleInvariant T=Real.sinh T.lengthA*Real.sinh (T.sideLineA.pointDist T.a) ∧
    halfTurnTriangleInvariant T=Real.sinh T.lengthB*Real.sinh (T.sideLineB.pointDist T.b) ∧
    halfTurnTriangleInvariant T=Real.sinh T.lengthC*Real.sinh (T.sideLineC.pointDist T.c) := by
  constructor
  · rw [halfTurnTriangleInvariant_eq_beta,triangle_sinh_height_A]
    ring
  · constructor
    · rw [halfTurnTriangleInvariant_eq_gamma,triangle_sinh_height_B]
      ring
    · rw [halfTurnTriangleInvariant,triangle_sinh_height_C]
      ring

end LowDimensionalTopology.Geometry.Hyperbolic
