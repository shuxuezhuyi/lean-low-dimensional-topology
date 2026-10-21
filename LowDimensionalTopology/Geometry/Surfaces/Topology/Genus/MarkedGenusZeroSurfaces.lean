/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannSphereTopology
public import LowDimensionalTopology.Geometry.Surfaces.Covering.SphereUniversalDeck
public import LowDimensionalTopology.Geometry.Surfaces.Topology.HandleModels

/-!
# Three marked points on a genuine genus-zero Riemann surface

The coordinate is obtained from the actual topological genus witness and
uniformization, then normalized by an actual Möbius transformation. Its
conjugation involution fixes the three given physical points. This does not
assert a lift of the involution through an orbifold quotient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Set Topology
open scoped OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- Actual genus zero gives an analytic sphere coordinate with analytic inverse. -/
theorem genus_zero_exists_analytic_sphere_coordinate {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (hg : HasTopologicalGenus X 0) :
    ∃ e : X ≃ₜ OnePoint ℂ,
      RiemannAnalyticMap R.toRiemannAtlas sphereRiemannAtlas e ∧
      RiemannAnalyticMap sphereRiemannAtlas R.toRiemannAtlas e.symm := by
  obtain ⟨f, hf, hbij⟩ :=
    (riemannSurface_conformallyEquivalent_sphere_iff_homeomorphic_twoSphere R).mpr
      (hasTopologicalGenus_zero_iff.mp hg)
  exact ⟨hf.toHomeomorph hbij, hf, hf.inverse_analytic hbij⟩

/-- Three distinct physical points on a genuine genus-zero surface admit a
normalized analytic sphere coordinate. No chosen conformal equivalence is a hypothesis. -/
theorem genus_zero_exists_normalized_analytic_coordinate {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (hg : HasTopologicalGenus X 0)
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ e : X ≃ₜ OnePoint ℂ,
      RiemannAnalyticMap R.toRiemannAtlas sphereRiemannAtlas e ∧
      e a = (0 : ℂ) ∧ e b = (1 : ℂ) ∧ e c = ∞ := by
  obtain ⟨f, hf, _⟩ := genus_zero_exists_analytic_sphere_coordinate R hg
  obtain ⟨q, hqa, hqb, hqc⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_normalize_triple (f a) (f b) (f c)
    ⟨fun h => hab (f.injective h), fun h => hac (f.injective h),
      fun h => hbc (f.injective h)⟩
  exact ⟨f.trans (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q),
    (mobius_riemannSphere_analytic q).comp hf, hqa, hqb, hqc⟩

/-- An analytic sphere coordinate is uniquely determined by the images of three
distinct physical points. -/
theorem analytic_sphere_coordinate_eq_of_marked_values {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (e f : X ≃ₜ OnePoint ℂ)
    (he : RiemannAnalyticMap R.toRiemannAtlas sphereRiemannAtlas e)
    (hf : RiemannAnalyticMap R.toRiemannAtlas sphereRiemannAtlas f)
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : e a = f a) (hb : e b = f b) (hc : e c = f c) : e = f := by
  let E := e.symm.trans f
  have hE : RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas E :=
    hf.comp (riemannAnalyticMap_homeomorph_symm e he)
  obtain ⟨M, hM, _⟩ := sphere_analytic_automorphism_existsUnique_mobius E hE
  have hfix (x : X) (hx : e x = f x) : M.val (e x) = e x := by
    rw [hM]
    change f (e.symm (e x)) = e x
    rw [e.symm_apply_apply]
    exact hx.symm
  have hM1 : M = 1 := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_of_agree_triple M 1 (e a) (e b) (e c)
    ⟨fun h => hab (e.injective h), fun h => hac (e.injective h),
      fun h => hbc (e.injective h)⟩ (hfix a ha) (hfix b hb) (hfix c hc)
  apply Homeomorph.ext
  intro x
  have hx := hM (e x)
  rw [hM1] at hx
  simpa [E] using hx

/-- The normalized analytic coordinate exists uniquely, rather than requiring
an arbitrary parameterization of the marked sphere as extra data. -/
theorem genus_zero_existsUnique_normalized_analytic_coordinate {X : Type*}
    [TopologicalSpace X] (R : RiemannSurface X) (hg : HasTopologicalGenus X 0)
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃! e : X ≃ₜ OnePoint ℂ,
      RiemannAnalyticMap R.toRiemannAtlas sphereRiemannAtlas e ∧
      e a = (0 : ℂ) ∧ e b = (1 : ℂ) ∧ e c = ∞ := by
  obtain ⟨e, he, ha, hb, hc⟩ :=
    genus_zero_exists_normalized_analytic_coordinate R hg a b c hab hac hbc
  refine ⟨e, ⟨he, ha, hb, hc⟩, ?_⟩
  rintro f ⟨hf, hfa, hfb, hfc⟩
  exact analytic_sphere_coordinate_eq_of_marked_values R f e hf he a b c hab hac hbc
    (hfa.trans ha.symm) (hfb.trans hb.symm) (hfc.trans hc.symm)

/-- Conjugation on the physical Riemann sphere, with infinity fixed. -/
def sphereConjugationHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  Complex.conjCLE.toHomeomorph.onePointCongr

@[simp] theorem sphereConjugationHomeomorph_coe (z : ℂ) :
    sphereConjugationHomeomorph (z : OnePoint ℂ) = (conj z : ℂ) := rfl

@[simp] theorem sphereConjugationHomeomorph_infty :
    sphereConjugationHomeomorph ∞ = ∞ := rfl

@[simp] theorem sphereConjugationHomeomorph_zero :
    sphereConjugationHomeomorph 0 = 0 := by
  change ((conj (0 : ℂ) : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
  simp

/-- The physical conjugation map is an involution. -/
theorem sphereConjugationHomeomorph_involutive :
    Function.Involutive sphereConjugationHomeomorph := by
  intro z
  induction z using OnePoint.rec <;> simp

/-- Physical sphere conjugation moves the ordinary point `I`. -/
theorem sphereConjugationHomeomorph_I_ne :
    sphereConjugationHomeomorph (Complex.I : ℂ) ≠ (Complex.I : ℂ) := by
  intro h
  have hi := congrArg Complex.im (OnePoint.coe_injective h)
  norm_num at hi

/-- Physical sphere conjugation is not a holomorphic map for the actual sphere atlas. -/
theorem sphereConjugationHomeomorph_not_analytic :
    ¬RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas sphereConjugationHomeomorph := by
  intro h
  obtain ⟨M, hM, _⟩ := sphere_analytic_automorphism_existsUnique_mobius
    sphereConjugationHomeomorph h
  have hM1 : M = 1 := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_one_of_fixes_zero_one_infty M
    (by simpa using hM ((0 : ℂ) : OnePoint ℂ))
    (by simpa using hM ((1 : ℂ) : OnePoint ℂ))
    (by simpa using hM ∞)
  have hi := hM (Complex.I : ℂ)
  rw [hM1] at hi
  exact sphereConjugationHomeomorph_I_ne hi.symm

/-- Reflection in an analytic sphere coordinate is a genuine surface homeomorphism. -/
def sphereCoordinateReflection {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ OnePoint ℂ) : X ≃ₜ X :=
  (e.trans sphereConjugationHomeomorph).trans e.symm

/-- Its coordinate expression is the actual extended complex conjugation. -/
theorem sphereCoordinateReflection_coordinate {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ OnePoint ℂ) (x : X) :
    e (sphereCoordinateReflection e x) = sphereConjugationHomeomorph (e x) :=
  e.apply_symm_apply _

/-- Reflection in the coordinate squares to identity on every physical point. -/
theorem sphereCoordinateReflection_involutive {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ OnePoint ℂ) : Function.Involutive (sphereCoordinateReflection e) := by
  intro x
  apply e.injective
  rw [sphereCoordinateReflection_coordinate, sphereCoordinateReflection_coordinate,
    sphereConjugationHomeomorph_involutive]

/-- Coordinate reflection fixes a point exactly when its sphere coordinate is real or infinity. -/
theorem sphereCoordinateReflection_fixed_iff {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ OnePoint ℂ) (x : X) :
    sphereCoordinateReflection e x = x ↔ sphereConjugationHomeomorph (e x) = e x := by
  rw [← e.injective.eq_iff, sphereCoordinateReflection_coordinate]

/-- The coordinate reflection is genuinely nontrivial. -/
theorem sphereCoordinateReflection_exists_moved {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ OnePoint ℂ) : ∃ x, sphereCoordinateReflection e x ≠ x := by
  refine ⟨e.symm (Complex.I : ℂ), ?_⟩
  intro h
  apply sphereConjugationHomeomorph_I_ne
  simpa only [e.apply_symm_apply] using (sphereCoordinateReflection_fixed_iff e _).mp h

/-- Reflection in an analytic sphere coordinate is not holomorphic for the
surface's original complex structure. -/
theorem sphereCoordinateReflection_not_analytic {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (e : X ≃ₜ OnePoint ℂ)
    (he : RiemannAnalyticMap R.toRiemannAtlas sphereRiemannAtlas e) :
    ¬RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas (sphereCoordinateReflection e) := by
  intro hr
  have hC := (he.comp hr).comp (riemannAnalyticMap_homeomorph_symm e he)
  have hfun : (fun z => e (sphereCoordinateReflection e (e.symm z))) =
      sphereConjugationHomeomorph := by
    funext z
    rw [sphereCoordinateReflection_coordinate, e.apply_symm_apply]
  exact sphereConjugationHomeomorph_not_analytic (hfun ▸ hC)

/-- Every three-point marked genus-zero Riemann surface has an involutive
reflection which is actual conjugation in a normalized analytic coordinate. -/
theorem genus_zero_exists_three_point_reflection {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (hg : HasTopologicalGenus X 0)
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ (e : X ≃ₜ OnePoint ℂ) (r : X ≃ₜ X),
      RiemannAnalyticMap R.toRiemannAtlas sphereRiemannAtlas e ∧
      RiemannAnalyticMap sphereRiemannAtlas R.toRiemannAtlas e.symm ∧
      e a = (0 : ℂ) ∧ e b = (1 : ℂ) ∧ e c = ∞ ∧
      Function.Involutive r ∧ r a = a ∧ r b = b ∧ r c = c ∧
      ∀ x, e (r x) = sphereConjugationHomeomorph (e x) := by
  obtain ⟨e, he, ha, hb, hc⟩ :=
    genus_zero_exists_normalized_analytic_coordinate R hg a b c hab hac hbc
  refine ⟨e, sphereCoordinateReflection e, he,
    riemannAnalyticMap_homeomorph_symm e he, ha, hb, hc,
    sphereCoordinateReflection_involutive e, ?_, ?_, ?_,
    sphereCoordinateReflection_coordinate e⟩
  · apply e.injective
    rw [sphereCoordinateReflection_coordinate, ha]
    change ((conj (0 : ℂ) : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
    simp
  · apply e.injective
    rw [sphereCoordinateReflection_coordinate, hb]
    simp
  · apply e.injective
    rw [sphereCoordinateReflection_coordinate, hc]
    rfl

end LowDimensionalTopology.Geometry.Surfaces
