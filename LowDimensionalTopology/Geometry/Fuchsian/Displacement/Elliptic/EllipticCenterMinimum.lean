/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.DisjointAxisConstraints
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane MatrixGroups Pointwise OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

set_option backward.isDefEq.respectTransparency false in
/-- Among the genuine images of one center distinct from the other center there is
a closest one, represented by a genuine lift in the original Fuchsian group. -/
theorem HalfPlaneFuchsianGroup.closest_distinct_native_orbit
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (u v : ℍ) (huv : u ≠ v) :
    ∃ C : Matrix.SpecialLinearGroup (Fin
      2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ H ∧ C • v ≠ u ∧
      ∀ D : Matrix.SpecialLinearGroup (Fin
        2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D ∈ H → D • v ≠ u →
        dist u (C • v) ≤ dist u (D • v) := by
  let ellipticCenterMinimumAction := P.nativeAction
  let ellipticCenterMinimumProper := P.native_properlyDiscontinuous
  let ellipticCenterMinimumIsometric : IsIsometricSMul H ℍ := ⟨fun g => (P.nativeHom g).isometry⟩
  have hstable (w : ℍ) (k : (⊥ : Subgroup H)) : (k.val • ·) '' ({w} : Set ℍ) = {w} := by
    have hk : k.val = 1 := Subgroup.mem_bot.mp k.property
    simp only [hk, one_smul, image_id']
  have hcover (w : ℍ) : ∀ x ∈ ({w} : Set ℍ),
      ∃ k : (⊥ : Subgroup H), ∃ c ∈ ({w} : Set ℍ), k.val • c = x := by
    intro x hx
    have hx' : x = w := mem_singleton_iff.mp hx
    refine ⟨1, w, rfl, ?_⟩
    simpa only [Subgroup.coe_one, one_smul] using hx'.symm
  have hne : ({v} : Set ℍ) ≠ {u} := by
    intro he
    exact huv (Set.singleton_injective he).symm
  obtain ⟨T, hT, hTne, x, hx, y, hy, hmin⟩ := compactCore_pair_minimizing_translates
    ({u} : Set ℍ) {v} {u} {v} (⊥ : Subgroup H) (⊥ : Subgroup H)
    isClosed_singleton (singleton_nonempty v) isCompact_singleton subset_rfl
    (singleton_nonempty u) isCompact_singleton (hstable u) (hcover u)
    (hstable v) (hcover v) hne
  obtain ⟨g, hTg⟩ := hT
  have hx' : x = u := mem_singleton_iff.mp hx
  have hy' : y = g • v := by
    rw [hTg, image_singleton] at hy
    exact mem_singleton_iff.mp hy
  obtain ⟨C, hC⟩ := mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
  have hCg : C • v = g • v := (P.nativeAction_realSL g C hC v).symm
  have hCv : C • v ≠ u := by
    intro he
    apply hTne
    rw [hTg, image_singleton, ← hCg, he]
  refine ⟨C, hC ▸ g.property, hCv, ?_⟩
  intro D hD hDv
  let d : H := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D, hD⟩
  have hdv : d • v = D • v := P.nativeAction_realSL d D rfl v
  have hUne : (d • ·) '' ({v} : Set ℍ) ≠ {u} := by
    rw [image_singleton, hdv]
    exact fun he => hDv (Set.singleton_injective he)
  have hm := hmin _ ⟨d, rfl⟩ hUne u rfl (d • v) (mem_image_of_mem _ (mem_singleton v))
  rwa [hx', hy', ← hCg, hdv] at hm

end LowDimensionalTopology.Geometry.Fuchsian
