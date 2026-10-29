module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.RectifiableMobiusLength
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization

/-!
# Full rectifiable length is independent of the continuous covering lift

Two actual continuous BV lifts of the same original parametrized curve differ
by one actual deck matrix on the connected compact parameter interval. Full
BV Möbius invariance therefore identifies their literal Poincaré arclengths,
including singular parameters, pauses and repeated traversals.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane Topology MatrixGroups ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- The original model's full rectifiable hyperbolic line integral has the
same value in any two genuine continuous BV lifts of the same parametrized
surface curve. No Lipschitz, C1, absolute continuity or unit-speed premise is
imposed on the original curves. -/
theorem HyperbolicSurfaceModel.rectifiable_lift_length_independent
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (c d : RectifiableCurve)
    (ha : c.a = d.a) (hb : c.b = d.b)
    (hcpos : ∀ t ∈ Icc c.a c.b, 0 < (c.curve t).im)
    (hdpos : ∀ t ∈ Icc c.a c.b, 0 < (d.curve t).im)
    (hprojection : ∀ (t : ℝ) (ht : t ∈ Icc c.a c.b),
      M.halfPlaneCover ⟨c.curve t, hcpos t ht⟩ =
        M.halfPlaneCover ⟨d.curve t, hdpos t ht⟩) :
    c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) =
      d.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  let J := Icc c.a c.b
  let : PreconnectedSpace J := Subtype.preconnectedSpace isPreconnected_Icc
  let f : C(J, ℍ) := ⟨fun t => ⟨c.curve t, hcpos t t.property⟩,
    Continuous.upperHalfPlaneMk
      (c.continuous.comp_continuous continuous_subtype_val (fun t => t.property)) _⟩
  have hdcont : ContinuousOn d.curve (Icc c.a c.b) := by
    simpa only [ha, hb] using d.continuous
  let g : C(J, ℍ) := ⟨fun t => ⟨d.curve t, hdpos t t.property⟩,
    Continuous.upperHalfPlaneMk
      (hdcont.comp_continuous continuous_subtype_val (fun t => t.property)) _⟩
  let a₀ : J := ⟨c.a, left_mem_Icc.mpr c.ordered⟩
  obtain ⟨A, hA, hA0⟩ := (hp.2.2.2 (f a₀) (g a₀)).1 (hprojection a₀ a₀.property)
  have hwhole : (fun t : J => A • f t) = g := by
    apply hp.1.eq_of_comp_eq ((continuous_const_smul A).comp f.continuous)
      g.continuous ?_ a₀ hA0
    funext t
    simp only [Function.comp_apply]
    exact ((hΓ A).mp hA (f t)).trans (hprojection t t.property)
  let m := c.mapHalfPlaneSL2 A hcpos
  have hm : EqOn m.curve d.curve (Icc m.a m.b) := by
    intro t ht
    let u : J := ⟨t, ht⟩
    have heq := congrArg ((↑) : ℍ → ℂ) (congrFun hwhole u)
    change halfPlaneSLComplexAction A (c.curve t) = d.curve t
    change ((A • UpperHalfPlane.ofComplex ((f u : ℍ) : ℂ) : ℍ) : ℂ) = d.curve t
    rw [UpperHalfPlane.ofComplex_apply]
    exact heq
  have hlength : m.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) =
      d.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by
    apply RectifiableCurve.weightedLength_eq_of_monotone_onto_reparam m d id
      (monotone_id.monotoneOn (Icc m.a m.b)) (by
        change id '' Icc c.a c.b = Icc d.a d.b
        simp only [image_id, ha, hb]) ha hb
    simpa only [Function.comp_id] using hm
  exact (c.mapHalfPlaneSL2_weightedLength A hcpos).symm.trans hlength

end LowDimensionalTopology.Geometry.Surfaces
