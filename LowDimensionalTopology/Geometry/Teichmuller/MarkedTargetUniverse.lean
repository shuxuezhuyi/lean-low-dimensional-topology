module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceUniverse
public import LowDimensionalTopology.Geometry.Teichmuller.RealizedBeltrami
public import Mathlib.Basic.Countable.Small
public import Mathlib.Topology.Instances.Shrink

/-!
# Actual smooth marked targets in every target universe

A finite cover by original complex charts gives a genuine surjection from
finitely many copies of the complex plane onto any closed surface carrier.
That proves smallness in every requested universe. The actual Shrink
homeomorphism transports the target's original complex atlas and the same
smooth oriented marking. Its literal tensor and uniform Banach coefficient
are unchanged. No raw-metric realization theorem is asserted here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

universe u w

/-- Compactness and the actual original chart cover make the carrier small
in every universe; no smallness or cardinality hypothesis is supplied. -/
theorem carrier_small {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) : Small.{w} X := by
  classical
  let := R.compactSpace
  choose e _he hx using R.cover
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (univ : Set X)).elim_finite_subcover
      (fun x : X => (e x).source) (fun x => (e x).open_source)
      (by
        intro x _
        exact mem_iUnion.mpr ⟨x, hx x⟩)
  let : Small.{w} ↥t := inferInstance
  apply small_of_surjective (f := fun p : ↥t × ℂ => (e p.1.val).symm p.2)
  intro x
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  exact ⟨(⟨i, hi⟩, e i x), (e i).left_inv hxi⟩

end LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v w

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- Transport the actual target atlas and the same smooth oriented marking to
an arbitrary requested target universe, keeping the reference surface fixed. -/
def retargetUniverse (M : MarkedRiemannSurface.{u, v} R) :
    MarkedRiemannSurface.{u, w} R := by
  letI : Small.{w} M.carrier := M.surface.carrier_small
  let p : Shrink.{w} M.carrier ≃ₜ M.carrier := (Shrink.homeomorph M.carrier).symm
  let S : ClosedRiemannSurface (Shrink.{w} M.carrier) :=
    M.surface.pullbackHomeomorph p
  have hp : RiemannAnalyticMap S.toRiemannAtlas M.surface.toRiemannAtlas p :=
    M.surface.pullbackHomeomorph_analytic p
  let f : SmoothSurfaceEquiv S.toRiemannSurface M.surface.toRiemannSurface :=
    .ofConformalHomeomorph S.toRiemannSurface M.surface.toRiemannSurface p hp
  have hf : PreservesComplexOrientation S.toRiemannAtlas M.surface.toRiemannAtlas
      f.toHomeomorph :=
    SmoothSurfaceEquiv.ofConformalHomeomorph_preservesComplexOrientation
      S.toRiemannSurface M.surface.toRiemannSurface p hp
  refine
    { carrier := Shrink.{w} M.carrier
      topology := inferInstance
      surface := S
      marking := M.marking.trans f.symm
      orientation_preserving := ?_ }
  exact (PreservesComplexOrientation.homeomorph_symm f.toHomeomorph hf).comp
    M.orientation_preserving M.marking.toHomeomorph.continuous

/-- The genuine target identification from the transported target to the
original target is the actual Shrink homeomorphism in the reverse direction. -/
def retargetUniverseProjection (M : MarkedRiemannSurface.{u, v} R) :
    (retargetUniverse.{u, v, w} M).carrier ≃ₜ M.carrier := by
  letI : Small.{w} M.carrier := M.surface.carrier_small
  exact (Shrink.homeomorph M.carrier).symm

/-- Atlas pullback proves analyticity of the actual target identification. -/
theorem retargetUniverseProjection_analytic (M : MarkedRiemannSurface.{u, v} R) :
    RiemannAnalyticMap (retargetUniverse.{u, v, w} M).surface.toRiemannAtlas
      M.surface.toRiemannAtlas (retargetUniverseProjection.{u, v, w} M) := by
  let : Small.{w} M.carrier := M.surface.carrier_small
  exact M.surface.pullbackHomeomorph_analytic (Shrink.homeomorph M.carrier).symm

/-- The same original identification also has an analytic inverse. -/
theorem retargetUniverseProjection_symm_analytic (M : MarkedRiemannSurface.{u, v} R) :
    RiemannAnalyticMap M.surface.toRiemannAtlas
      (retargetUniverse.{u, v, w} M).surface.toRiemannAtlas
      (retargetUniverseProjection.{u, v, w} M).symm :=
  riemannAnalyticMap_homeomorph_symm (retargetUniverseProjection.{u, v, w} M)
    (retargetUniverseProjection_analytic M)

/-- Projecting the transported marking recovers the original marking exactly
at every original reference point, without a homotopy replacement. -/
@[simp]
theorem retargetUniverseProjection_marking (M : MarkedRiemannSurface.{u, v} R) (x : X) :
    retargetUniverseProjection.{u, v, w} M
      ((retargetUniverse.{u, v, w} M).marking.toHomeomorph x) =
        M.marking.toHomeomorph x := by
  let : Small.{w} M.carrier := M.surface.carrier_small
  let p : Shrink.{w} M.carrier ≃ₜ M.carrier := (Shrink.homeomorph M.carrier).symm
  change p (p.symm (M.marking.toHomeomorph x)) = M.marking.toHomeomorph x
  exact p.apply_symm_apply _

/-- The actual continuous tensor is unchanged by the exact analytic target
identification, for independently sized original and transported targets. -/
@[simp]
theorem retargetUniverse_beltramiTensor (M : MarkedRiemannSurface.{u, v} R) :
    (retargetUniverse.{u, v, w} M).beltramiTensor = M.beltramiTensor := by
  let N : MarkedRiemannSurface.{u, w} R := retargetUniverse M
  change N.marking.beltrami N.orientation_preserving =
    M.marking.beltrami M.orientation_preserving
  exact (N.marking.beltrami_eq_iff_exists_analytic_homeomorph M.marking
    N.orientation_preserving M.orientation_preserving).2
      ⟨retargetUniverseProjection.{u, v, w} M,
        retargetUniverseProjection_analytic M,
        retargetUniverseProjection_symm_analytic M,
        retargetUniverseProjection_marking M⟩

/-- Every original chart reads the same literal pointwise coefficient after
target transport, at every point of that chart's actual coordinate range. -/
theorem retargetUniverse_rawBeltramiCoefficient
    (M : MarkedRiemannSurface.{u, v} R)
    (e : BeltramiDifferential.Chart R.toRiemannAtlas) (z : e.val.target) :
    (retargetUniverse.{u, v, w} M).marking.rawBeltramiCoefficient e z.val =
      M.marking.rawBeltramiCoefficient e z.val := by
  exact congrArg (fun μ : BeltramiDifferential R.toRiemannAtlas => μ.coeff e z)
    (retargetUniverse_beltramiTensor.{u, v, w} M)

/-- The genuine uniform Banach coefficient is preserved as an actual element
of the same original source coefficient space. -/
@[simp]
theorem retargetUniverse_beltramiCoefficient (M : MarkedRiemannSurface.{u, v} R) :
    (retargetUniverse.{u, v, w} M).beltramiCoefficient = M.beltramiCoefficient := by
  let := R.compactSpace
  change BeltramiDifferential.ofTensor (retargetUniverse.{u, v, w} M).beltramiTensor =
    BeltramiDifferential.ofTensor M.beltramiTensor
  exact congrArg BeltramiDifferential.ofTensor (retargetUniverse_beltramiTensor M)

end MarkedRiemannSurface

/-- The actual range of smooth marked coefficients is independent of the
chosen target universe, by retargeting each genuine marked witness. -/
theorem realizedBeltramiSet_universe_eq {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) :
    realizedBeltramiSet.{u, v} R = realizedBeltramiSet.{u, w} R := by
  apply Set.ext
  intro μ
  change (∃ M : MarkedRiemannSurface.{u, v} R, M.beltramiCoefficient = μ) ↔
    (∃ M : MarkedRiemannSurface.{u, w} R, M.beltramiCoefficient = μ)
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨MarkedRiemannSurface.retargetUniverse.{u, v, w} M,
      MarkedRiemannSurface.retargetUniverse_beltramiCoefficient M⟩
  · rintro ⟨M, rfl⟩
    exact ⟨MarkedRiemannSurface.retargetUniverse.{u, w, v} M,
      MarkedRiemannSurface.retargetUniverse_beltramiCoefficient M⟩

end LowDimensionalTopology.Geometry.Teichmuller
