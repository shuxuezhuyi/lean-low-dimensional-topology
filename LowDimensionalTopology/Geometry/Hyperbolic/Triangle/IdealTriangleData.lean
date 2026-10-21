/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleRays
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleTrigonometry
public import Mathlib.Basic.ENNReal.Basic

/-!
# Actual finite and ideal triangle side and angle data
-/

@[expose] public section
open Set
open scoped UpperHalfPlane Complex.UnitDisc ENNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

def closedDiscFinitePoint (p : 𝕔𝔻) (hp : ‖(p : ℂ)‖ < 1) : 𝔻 :=
  Complex.UnitDisc.mk (p : ℂ) hp

theorem closedDiscFinitePoint_spec (p : 𝕔𝔻) (hp : ‖(p : ℂ)‖ < 1) :
    discToClosedModel (closedDiscFinitePoint p hp) = p := by
  apply Subtype.ext
  rfl

/-- The source side-length convention: the native path distance when both endpoints
are finite, and infinity when an endpoint is ideal. This is not a metric on the compactification. -/
def extendedDiscSideLength (p q : 𝕔𝔻) : ℝ≥0∞ :=
  if hp : ‖(p : ℂ)‖ < 1 then
    if hq : ‖(q : ℂ)‖ < 1 then
      ENNReal.ofReal (discPathDist (closedDiscFinitePoint p hp) (closedDiscFinitePoint q hq))
    else ∞
  else ∞

theorem extendedDiscSideLength_finite (z w : 𝔻) :
    extendedDiscSideLength (discToClosedModel z) (discToClosedModel w) =
      ENNReal.ofReal (discPathDist z w) := by
  have hz : ‖((discToClosedModel z : 𝕔𝔻) : ℂ)‖ < 1 := z.norm_lt_one
  have hw : ‖((discToClosedModel w : 𝕔𝔻) : ℂ)‖ < 1 := w.norm_lt_one
  rw [extendedDiscSideLength,dite_eq_left hz,dite_eq_left hw]
  rfl

theorem extendedDiscSideLength_ideal_left (p q : 𝕔𝔻) (hp : ‖(p : ℂ)‖ = 1) :
    extendedDiscSideLength p q = ∞ := by
  simp [extendedDiscSideLength,hp]

theorem extendedDiscSideLength_ideal_right (p q : 𝕔𝔻) (hq : ‖(q : ℂ)‖ = 1) :
    extendedDiscSideLength p q = ∞ := by
  unfold extendedDiscSideLength
  by_cases hp : ‖(p : ℂ)‖ < 1
  · rw [dite_eq_left hp,dite_eq_right (by rw [hq]; exact lt_irrefl (1 : ℝ))]
  · rw [dite_eq_right hp]

def ClosedDiscTriangle.cycle (T : ClosedDiscTriangle) : ClosedDiscTriangle where
  a := T.b
  b := T.c
  c := T.a
  noncollinear := by
    rintro ⟨L,hb,hc,ha⟩
    exact T.noncollinear ⟨L,ha,hb,hc⟩

theorem ClosedDiscTriangle.cycle_three (T : ClosedDiscTriangle) : T.cycle.cycle.cycle = T := by
  cases T
  rfl

def ClosedDiscTriangle.lengthA (T : ClosedDiscTriangle) : ℝ≥0∞ := extendedDiscSideLength T.b T.c
def ClosedDiscTriangle.lengthB (T : ClosedDiscTriangle) : ℝ≥0∞ := extendedDiscSideLength T.c T.a
def ClosedDiscTriangle.lengthC (T : ClosedDiscTriangle) : ℝ≥0∞ := extendedDiscSideLength T.a T.b

/-- At a finite vertex the angle is the actual forward-tangent angle of the genuine corner;
the angle at an ideal vertex is zero by the source convention. -/
def ClosedDiscTriangle.alpha (T : ClosedDiscTriangle) : ℝ :=
  if ha : ‖(T.a : ℂ)‖ < 1 then
    discInteriorAngleMeasure
      (T.cornerRayABAtA (closedDiscFinitePoint T.a ha) (closedDiscFinitePoint_spec T.a ha).symm)
      (T.cornerRayACAtA (closedDiscFinitePoint T.a ha) (closedDiscFinitePoint_spec T.a ha).symm)
  else 0

def ClosedDiscTriangle.beta (T : ClosedDiscTriangle) : ℝ := T.cycle.alpha
def ClosedDiscTriangle.gamma (T : ClosedDiscTriangle) : ℝ := T.cycle.cycle.alpha

theorem ClosedDiscTriangle.alpha_of_finite (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    T.alpha = discInteriorAngleMeasure (T.cornerRayABAtA z ha) (T.cornerRayACAtA z ha) := by
  have hz : ‖(T.a : ℂ)‖ < 1 := by rw [ha]; exact z.norm_lt_one
  rw [ClosedDiscTriangle.alpha,dite_eq_left hz]
  have he : closedDiscFinitePoint T.a hz = z := by
    apply Complex.UnitDisc.coe_injective
    exact congrArg (fun p : 𝕔𝔻 => (p : ℂ)) ha
  subst z
  rfl

theorem ClosedDiscTriangle.alpha_of_ideal (T : ClosedDiscTriangle) (ha : ‖(T.a : ℂ)‖ = 1) :
    T.alpha = 0 := by
  simp [ClosedDiscTriangle.alpha,ha]

theorem ClosedDiscTriangle.beta_of_ideal (T : ClosedDiscTriangle) (hb : ‖(T.b : ℂ)‖ = 1) :
    T.beta = 0 := T.cycle.alpha_of_ideal hb

theorem ClosedDiscTriangle.gamma_of_ideal (T : ClosedDiscTriangle) (hc : ‖(T.c : ℂ)‖ = 1) :
    T.gamma = 0 := T.cycle.cycle.alpha_of_ideal hc

theorem ClosedDiscTriangle.ideal_vertex_data (T : ClosedDiscTriangle) (ha : ‖(T.a : ℂ)‖ = 1) :
    T.alpha = 0 ∧ T.lengthB = ∞ ∧ T.lengthC = ∞ :=
  ⟨T.alpha_of_ideal ha,extendedDiscSideLength_ideal_right T.c T.a ha,
    extendedDiscSideLength_ideal_left T.a T.b ha⟩

theorem ClosedDiscTriangle.two_ideal_vertices_lengths (T : ClosedDiscTriangle)
    (ha : ‖(T.a : ℂ)‖ = 1) (hb : ‖(T.b : ℂ)‖ = 1) :
    T.lengthA = ∞ ∧ T.lengthB = ∞ ∧ T.lengthC = ∞ :=
  ⟨extendedDiscSideLength_ideal_left T.b T.c hb,
    extendedDiscSideLength_ideal_right T.c T.a ha,
    extendedDiscSideLength_ideal_left T.a T.b ha⟩

theorem DiscTriangle.closed_lengths (T : DiscTriangle) :
    T.toClosedDiscTriangle.lengthA = ENNReal.ofReal T.lengthA ∧
      T.toClosedDiscTriangle.lengthB = ENNReal.ofReal T.lengthB ∧
        T.toClosedDiscTriangle.lengthC = ENNReal.ofReal T.lengthC :=
  ⟨extendedDiscSideLength_finite T.b T.c,extendedDiscSideLength_finite T.c T.a,
    extendedDiscSideLength_finite T.a T.b⟩

theorem DiscTriangle.closed_alpha (T : DiscTriangle) : T.toClosedDiscTriangle.alpha = T.alpha := by
  rw [T.toClosedDiscTriangle.alpha_of_finite T.a rfl,
    T.cornerRayABAtA_toClosedDiscTriangle,T.cornerRayACAtA_toClosedDiscTriangle]
  rfl

def DiscTriangle.cycle (T : DiscTriangle) : DiscTriangle where
  a := T.b
  b := T.c
  c := T.a
  noncollinear := by
    rintro ⟨L,hb,hc,ha⟩
    exact T.noncollinear ⟨L,ha,hb,hc⟩

theorem DiscTriangle.toClosed_cycle (T : DiscTriangle) :
    T.cycle.toClosedDiscTriangle = T.toClosedDiscTriangle.cycle := by
  cases T
  rfl

theorem DiscTriangle.cycle_alpha (T : DiscTriangle) : T.cycle.alpha = T.beta :=
  InnerProductGeometry.angle_comm _ _

theorem DiscTriangle.cycle_cycle_alpha (T : DiscTriangle) : T.cycle.cycle.alpha = T.gamma := rfl

theorem DiscTriangle.closed_angles (T : DiscTriangle) :
    T.toClosedDiscTriangle.alpha = T.alpha ∧ T.toClosedDiscTriangle.beta = T.beta ∧
      T.toClosedDiscTriangle.gamma = T.gamma := by
  refine ⟨T.closed_alpha,?_,?_⟩
  · change T.toClosedDiscTriangle.cycle.alpha = T.beta
    rw [← T.toClosed_cycle,T.cycle.closed_alpha,T.cycle_alpha]
  · change T.toClosedDiscTriangle.cycle.cycle.alpha = T.gamma
    rw [← T.toClosed_cycle,← T.cycle.toClosed_cycle,T.cycle.cycle.closed_alpha,T.cycle_cycle_alpha]

theorem ClosedDiscTriangle.alpha_bounds_of_finite (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) : T.alpha ∈ Ioo (0 : ℝ) Real.pi := by
  rw [T.alpha_of_finite z ha]
  have hproper := T.cornerAtA_proper z ha
  constructor
  · rw [discInteriorAngleMeasure_eq_halfPlane]
    exact hInteriorAngleMeasure_pos _ _
      (((T.cornerRayABAtA z ha).different_supports_iff (T.cornerRayACAtA z ha)).mp hproper)
  · exact (discInteriorAngleMeasure_mem_Ico _ _ hproper).2

theorem ClosedDiscTriangle.alpha_pos_iff_finite (T : ClosedDiscTriangle) :
    0 < T.alpha ↔ ‖(T.a : ℂ)‖ < 1 := by
  by_cases ha : ‖(T.a : ℂ)‖ < 1
  · exact ⟨fun _ => ha,fun _ =>
      (T.alpha_bounds_of_finite (closedDiscFinitePoint T.a ha)
        (closedDiscFinitePoint_spec T.a ha).symm).1⟩
  · have ha' : ‖(T.a : ℂ)‖ = 1 := le_antisymm T.a.norm_le_one (not_lt.mp ha)
    rw [T.alpha_of_ideal ha']
    exact ⟨fun h => (lt_irrefl (0 : ℝ) h).elim,fun h => (ha h).elim⟩

theorem ClosedDiscTriangle.alpha_eq_zero_iff_ideal (T : ClosedDiscTriangle) :
    T.alpha = 0 ↔ ‖(T.a : ℂ)‖ = 1 := by
  constructor
  · intro he
    apply le_antisymm T.a.norm_le_one
    by_contra! ha
    have hpos := T.alpha_pos_iff_finite.mpr ha
    rw [he] at hpos
    exact lt_irrefl (0 : ℝ) hpos
  · exact T.alpha_of_ideal

theorem closedModelCayley_norm_one_iff (p : ClosedHalfPlaneModel) :
    ‖(closedModelCayleyHomeomorph p : ℂ)‖ = 1 ↔ p.val ∈ halfPlaneIdealBoundary := by
  rw [idealBoundary_cayley_iff,← closedModelCayley_toExtended]
  exact (coe_mem_extendedDiscIdealBoundary (closedModelCayleyHomeomorph p : ℂ)).symm

def ClosedHTriangle.lengthA (T : ClosedHTriangle) : ℝ≥0∞ := T.toDiscTriangle.lengthA
def ClosedHTriangle.lengthB (T : ClosedHTriangle) : ℝ≥0∞ := T.toDiscTriangle.lengthB
def ClosedHTriangle.lengthC (T : ClosedHTriangle) : ℝ≥0∞ := T.toDiscTriangle.lengthC
def ClosedHTriangle.alpha (T : ClosedHTriangle) : ℝ := T.toDiscTriangle.alpha
def ClosedHTriangle.beta (T : ClosedHTriangle) : ℝ := T.toDiscTriangle.beta
def ClosedHTriangle.gamma (T : ClosedHTriangle) : ℝ := T.toDiscTriangle.gamma

theorem ClosedHTriangle.ideal_vertex_data (T : ClosedHTriangle) (ha : T.a.val ∈ halfPlaneIdealBoundary) :
    T.alpha = 0 ∧ T.lengthB = ∞ ∧ T.lengthC = ∞ :=
  T.toDiscTriangle.ideal_vertex_data ((closedModelCayley_norm_one_iff T.a).mpr ha)

theorem ClosedHTriangle.two_ideal_vertices_lengths (T : ClosedHTriangle)
    (ha : T.a.val ∈ halfPlaneIdealBoundary) (hb : T.b.val ∈ halfPlaneIdealBoundary) :
    T.lengthA = ∞ ∧ T.lengthB = ∞ ∧ T.lengthC = ∞ :=
  T.toDiscTriangle.two_ideal_vertices_lengths ((closedModelCayley_norm_one_iff T.a).mpr ha)
    ((closedModelCayley_norm_one_iff T.b).mpr hb)

theorem HTriangle.closed_lengths (T : HTriangle) :
    T.toClosedHTriangle.lengthA = ENNReal.ofReal T.lengthA ∧
      T.toClosedHTriangle.lengthB = ENNReal.ofReal T.lengthB ∧
        T.toClosedHTriangle.lengthC = ENNReal.ofReal T.lengthC := by
  simpa only [ClosedHTriangle.lengthA,ClosedHTriangle.lengthB,ClosedHTriangle.lengthC,
    T.toClosedHTriangle_toDiscTriangle,T.toDiscTriangle.lengths_eq_halfPlane.1,
    T.toDiscTriangle.lengths_eq_halfPlane.2.1,T.toDiscTriangle.lengths_eq_halfPlane.2.2,
    T.toDiscTriangle_toHalfPlane] using T.toDiscTriangle.closed_lengths

theorem HTriangle.closed_angles (T : HTriangle) :
    T.toClosedHTriangle.alpha = T.alpha ∧ T.toClosedHTriangle.beta = T.beta ∧
      T.toClosedHTriangle.gamma = T.gamma := by
  simpa only [ClosedHTriangle.alpha,ClosedHTriangle.beta,ClosedHTriangle.gamma,
    T.toClosedHTriangle_toDiscTriangle,T.toDiscTriangle.angles_eq_halfPlane.1,
    T.toDiscTriangle.angles_eq_halfPlane.2.1,T.toDiscTriangle.angles_eq_halfPlane.2.2,
    T.toDiscTriangle_toHalfPlane] using T.toDiscTriangle.closed_angles

end
end LowDimensionalTopology.Geometry.Hyperbolic
