module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeComplexMinimizers
public import LowDimensionalTopology.Geometry.Teichmuller.NativeModularProperAction
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite order in the elliptic direction

The original full modular group has finite point stabilizers by its proved
finite-ball transporter theorem. A zero attained displacement is a genuine
fixed point in the full-log metric. No converse realization is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Surfaces LiZhongQC
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

local notation "QCPointR" => @TeichSpace X _ R.toRiemannAtlas.toChartedSpace
local notation "ModularR" =>
  @SourceQCModular.ModularGroup X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold

/-- Finiteness concerns all actual modular classes, including any ineffective kernel. -/
theorem modular_stabilizer_finite {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (p : QCPointR) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    (MulAction.stabilizer ModularR p : Set ModularR).Finite := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨Γ, p₀, _, _, hp₀⟩ :=
    s22hg_exists_fuchsian_uniformization (S := X) hg (R.hasSourceGenus hgenus)
  have hfin := SourceQCModular.finite_ball_transporter hg (R.hasSourceGenus hgenus) hp₀ p 1
  apply hfin.subset
  intro γ hγ
  refine ⟨p, ?_, ?_⟩
  · rw [s29_m_teichDistance_self]
    exact zero_lt_one
  · rw [MulAction.mem_stabilizer_iff.mp hγ, s29_m_teichDistance_self]
    exact zero_lt_one

/-- Ellipticity of the actual modular class implies finite order. -/
theorem isOfFinOrder_of_isElliptic {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (γ : ModularR) (hγ : IsElliptic R γ) : IsOfFinOrder γ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
  obtain ⟨hzero, p, hp⟩ := hγ
  have hd : displacement R γ p = 0 := hp.symm.trans hzero
  have hfix : γ • p = p :=
    (dist_eq_zero.mp (show dist p (γ • p) = 0 from hd)).symm
  let S := MulAction.stabilizer ModularR p
  have hS : (S : Set ModularR).Finite := modular_stabilizer_finite R hg hgenus p
  let : Fintype S := hS.fintype
  let γS : S := ⟨γ, hfix⟩
  exact S.subtype.isOfFinOrder (isOfFinOrder_of_finite γS)

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
