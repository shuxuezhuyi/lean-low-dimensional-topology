module

public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TwoIdealTriangleDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ThreeIdealTriangleDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleVertexTessellation

set_option autoImplicit false

@[expose] public section

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set
  Topology
open scoped UpperHalfPlane

/-- The actual all-finite integral-angle case, transported from the genuine compact triangle. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_finite_integral
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p q r : ℕ) (hp : 2≤p) (hq : 2≤q) (hr : 2≤r)
    (ha : T.alpha=Real.pi/(p:ℝ)) (hb : T.beta=Real.pi/(q:ℝ))
    (hc : T.gamma=Real.pi/(r:ℝ)) : DiscreteTopology (triangleReflectionGroup T) := by
  have hp0 : 0<(p:ℝ):=by positivity
  have hq0 : 0<(q:ℝ):=by positivity
  have hr0 : 0<(r:ℝ):=by positivity
  obtain ⟨U,huA,huB,huC⟩:=exists_finite_triangle_with_angles T.alpha T.beta T.gamma
    (by rw [ha]; exact div_pos Real.pi_pos hp0) (by rw [hb]; exact div_pos Real.pi_pos hq0)
    (by rw [hc]; exact div_pos Real.pi_pos hr0) T.angle_sum_lt_pi
  let n : Fin 3→ℕ:=![p,q,r]
  have hn : ∀i,2≤n i:=by intro i;fin_cases i <;> assumption
  have hu : ∀i,finiteTriangleVertexAngle U i=Real.pi/(n i:ℝ):=by
    intro i
    fin_cases i
    · exact huA.trans ha
    · exact huB.trans hb
    · exact huC.trans hc
  have hd : DiscreteTopology (triangleReflectionGroup U.toClosedHTriangle):=by
    rw [←finiteTrianglePoincarePairing_generated]
    exact (finiteTriangle_integral_poincare U n hn hu).1
  let : DiscreteTopology (triangleReflectionGroup U.toClosedHTriangle):=hd
  obtain ⟨e,he⟩:=equal_angle_triangle_reflectionGroups_conjugate T U.toClosedHTriangle
    ((U.closed_angles.1.trans huA).symm) ((U.closed_angles.2.1.trans huB).symm)
    ((U.closed_angles.2.2.trans huC).symm)
  have hconj : DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e⁻¹ (triangleReflectionGroup U.toClosedHTriangle)):=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete e⁻¹ (triangleReflectionGroup U.toClosedHTriangle)
  rw [←he,native_subgroupConjugate_compose,inv_mul_cancel,native_subgroupConjugate_one] at hconj
  exact hconj

/-- A source integral-submultiple angle includes the genuine ideal angle zero. -/
def IsIntegralTriangleAngle (θ : ℝ) : Prop:=θ=0 ∨ ∃n : ℕ,2≤n ∧ θ=Real.pi/(n:ℝ)

theorem triangleOrderAngle_isIntegral (p : ℕ∞) (hp : 2≤p) :
    IsIntegralTriangleAngle (triangleOrderAngle p) := by
  induction p using ENat.recTopCoe with
  | top => exact Or.inl triangleOrderAngle_top
  | coe n => exact Or.inr ⟨n,by exact_mod_cast hp,triangleOrderAngle_nat n⟩

/-- Integral-submultiple angles suffice for discreteness of the original three-mirror triangle group,
with every finite and ideal vertex configuration included. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_integral_angles
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha : IsIntegralTriangleAngle T.alpha) (hb : IsIntegralTriangleAngle T.beta)
    (hc : IsIntegralTriangleAngle T.gamma) : DiscreteTopology (triangleReflectionGroup T) := by
  have h1:=closedHTriangle_cycle_angles T
  have h2:=closedHTriangle_cycle_angles T.cycle
  rcases ha with ha|⟨p,hp,ha⟩ <;> rcases hb with hb|⟨q,hq,hb⟩ <;> rcases hc with hc|⟨r,hr,hc⟩
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_three_ideal T ha hb hc
  · have hd:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_two_ideal T.cycle.cycle r hr
      (h2.1.trans (h1.2.1.trans hc)) (h2.2.1.trans (h1.2.2.trans ha)) (h2.2.2.trans (h1.1.trans hb))
    repeat rw [triangleReflectionGroup_cycle] at hd
    exact hd
  · have hd:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_two_ideal T.cycle q hq
      (h1.1.trans hb) (h1.2.1.trans hc) (h1.2.2.trans ha)
    repeat rw [triangleReflectionGroup_cycle] at hd
    exact hd
  · have hd:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_one_ideal_integral_all T.cycle q r hq hr
      (h1.1.trans hb) (h1.2.1.trans hc) (h1.2.2.trans ha)
    repeat rw [triangleReflectionGroup_cycle] at hd
    exact hd
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_two_ideal T p hp ha hb hc
  · have hd:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_one_ideal_integral_all T.cycle.cycle r p hr hp
      (h2.1.trans (h1.2.1.trans hc)) (h2.2.1.trans (h1.2.2.trans ha)) (h2.2.2.trans (h1.1.trans hb))
    repeat rw [triangleReflectionGroup_cycle] at hd
    exact hd
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_one_ideal_integral_all T p q hp hq ha hb hc
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_finite_integral T p q r hp hq hr ha hb hc

/-- The conformal subgroup has precisely the same full-scope sufficient discreteness criterion. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_integral_angles
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha : IsIntegralTriangleAngle T.alpha) (hb : IsIntegralTriangleAngle T.beta)
    (hc : IsIntegralTriangleAngle T.gamma) : DiscreteTopology (triangleConformalGroup T) :=
  (triangle_discrete_full_iff_conformal T).mp
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_integral_angles T ha hb hc)

/-- Every genuine triangle group of reciprocal integer-or-infinite orders is discrete. -/
theorem IsTriangleGroupOfOrders.discrete {G : Subgroup (ℍ≃ᵢℍ)} {p q r : ℕ∞}
    (hG : IsTriangleGroupOfOrders G p q r) : DiscreteTopology G := by
  obtain ⟨hp,hq,hr,T,ha,hb,hc,rfl⟩:=hG
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_integral_angles T
  · rw [ha]
    exact triangleOrderAngle_isIntegral p hp
  · rw [hb]
    exact triangleOrderAngle_isIntegral q hq
  · rw [hc]
    exact triangleOrderAngle_isIntegral r hr

end LowDimensionalTopology.Geometry.Fuchsian
