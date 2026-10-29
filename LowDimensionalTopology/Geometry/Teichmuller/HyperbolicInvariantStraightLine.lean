module

public import LowDimensionalTopology.Geometry.Teichmuller.ConditionalInvariantStraightLine
public import LowDimensionalTopology.Geometry.Teichmuller.NativeModularDisplacementTypes

/-!
# Hyperbolic modular transformations and invariant straight lines

The full original QC modular group acts on its actual marked quotient with
the full-log metric. For a nonperiodic element, the pointwise minimizing-line
equivalence and the finite-order consequence of ellipticity give the global
hyperbolic-line criterion under the explicit straight-line geometry input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Set Surfaces LiZhongQC
open LowDimensionalTopology.Unproved.Teichmuller

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

local notation "QCPointR" => @TeichSpace X _ R.toRiemannAtlas.toChartedSpace
local notation "ModularR" =>
  @SourceQCModular.ModularGroup X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold

/-- A nonperiodic original modular class is hyperbolic exactly when it preserves
an actual full-log isometric line, with the straight-line input explicit. -/
theorem isHyperbolic_iff_exists_invariantLine_of_straightLineGeometry
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hgeometry : OriginalTeichmullerStraightLineGeometry R hg hgenus)
    (γ : ModularR) (hγ : ¬ IsOfFinOrder γ) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := R.compactSpace
    letI := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
    IsHyperbolic R γ ↔
      ∃ ℓ : ℝ → QCPointR, Isometry ℓ ∧
        (fun q : QCPointR => γ • q) '' range ℓ = range ℓ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
  constructor
  · rintro ⟨_, p, hp⟩
    obtain ⟨ℓ, hℓ, _, hinvariant⟩ :=
      (isMinimizingPoint_iff_exists_invariantLine_of_straightLineGeometry
        R hg hgenus hgeometry γ hγ p).mp hp
    exact ⟨ℓ, hℓ, hinvariant⟩
  · rintro ⟨ℓ, hℓ, hinvariant⟩
    have hp : IsMinimizingPoint R γ (ℓ 0) :=
      (isMinimizingPoint_iff_exists_invariantLine_of_straightLineGeometry
        R hg hgenus hgeometry γ hγ (ℓ 0)).mpr ⟨ℓ, hℓ, ⟨0, rfl⟩, hinvariant⟩
    have hnonzero : infimalDisplacement R γ ≠ 0 := by
      intro hzero
      exact hγ (isOfFinOrder_of_isElliptic R hg hgenus γ ⟨hzero, ℓ 0, hp⟩)
    exact ⟨lt_of_le_of_ne (infimalDisplacement_nonneg R γ) (Ne.symm hnonzero), ℓ 0, hp⟩

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
