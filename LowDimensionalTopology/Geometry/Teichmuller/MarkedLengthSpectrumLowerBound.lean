/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0), through the
project's original free-length and marked-length interfaces;
see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedLengthSpectrum
public import Mathlib.Topology.MetricSpace.Basic

/-!
# A uniform positive bound for each complete marked length spectrum

Every coordinate of one actual marked spectrum is a positive value of the
same original target's closed free-length spectrum. Since that spectrum is
closed and omits zero, one positive neighborhood of zero avoids all those
coordinates at once. No finite curve selection is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)

/-- Every original marked point has a positive bound shared by all of its
essential unoriented simple free-class length coordinates. -/
theorem markedLengthSpectrum_uniformly_pos (t : TeichmullerSpace.{0, 0} R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : EssentialSimpleFreeClass X,
      ε ≤ (markedLengthSpectrum R hg hgenus t a : ℝ) := by
  obtain ⟨m, rfl⟩ := Quotient.exists_rep t
  change ∃ ε : ℝ, 0 < ε ∧ ∀ a : EssentialSimpleFreeClass X,
    ε ≤ (markedLengthSpectrum R hg hgenus (TeichmullerSpace.mk m) a : ℝ)
  let := m.surface.toRiemannAtlas.toChartedSpace
  let M := m.geodesicLengthModel R hg hgenus
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  let S : Set ℝ := positiveFreeLengthSpectrum M.halfPlaneCover
  have hS : IsClosed S :=
    (m.surface.positiveFreeLengthSpectrum_closed_discrete M.halfPlaneCover hp).1
  have hzero : (0 : ℝ) ∈ Sᶜ := by
    intro h
    exact (lt_irrefl (0 : ℝ)) h.1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hS.isOpen_compl.mem_nhds hzero)
  have hmember (a : EssentialSimpleFreeClass X) :
      (markedLengthSpectrum R hg hgenus (TeichmullerSpace.mk m) a : ℝ) ∈ S := by
    obtain ⟨c, rfl⟩ := Quotient.exists_rep a
    let α : LiZhongQC.Loop X := circleRepresentativeLoop c.1
    let β : LiZhongQC.Loop m.carrier :=
      ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩
    have hpos : 0 < (markedLoopLength R hg hgenus α m).toReal :=
      markedGeodesicLength_pos R hg hgenus α (essentialSimpleCircle_loop_not_null c)
        (TeichmullerSpace.mk m)
    change (markedLoopLength R hg hgenus α m).toReal ∈
      positiveFreeLengthSpectrum M.halfPlaneCover
    refine ⟨hpos, Quotient.mk (freeLoopSetoid m.carrier) β, ?_⟩
    change markedLoopLength R hg hgenus α m =
      ENNReal.ofReal (markedLoopLength R hg hgenus α m).toReal
    exact (ENNReal.ofReal_toReal (markedLoopLength_ne_top R hg hgenus α m)).symm
  refine ⟨ε, hε, fun a => le_of_not_gt fun hlt => ?_⟩
  have ha := hmember a
  apply (hball ?_) ha
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha.1] using hlt

end LowDimensionalTopology.Geometry.Teichmuller
