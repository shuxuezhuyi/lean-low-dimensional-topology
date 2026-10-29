module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalRegions

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- Reversing the same actual lift inverts its full covering element. -/
theorem covers_reverse {S : Type} [TopologicalSpace S] {p : ℍ → S}
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} {α : LiZhongQC.Loop S}
    (hcov : LiZhongQC.Covers p A α) :
    LiZhongQC.Covers p A⁻¹ ⟨α.1, α.2.symm⟩ := by
  obtain ⟨c, hcc, hcp, hc1⟩ := hcov
  have htime : Set.MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨fun t => c (1 - t),
    hcc.comp (continuous_const.sub continuous_id).continuousOn htime, ?_, ?_⟩
  · intro t ht
    rw [Path.extend_symm_apply]
    exact hcp (1 - t) (htime ht)
  · simp only [sub_self, sub_zero]
    rw [hc1, inv_smul_smul]

/-- The entire free-class length on one uniformized original cover ignores reversal. -/
theorem freeHomotopyLength_reverse {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : LiZhongQC.IsUniformization Γ p) (α : LiZhongQC.Loop S) :
    LiZhongQC.freeHomotopyLength p ⟨α.1, α.2.symm⟩ =
      LiZhongQC.freeHomotopyLength p α := by
  obtain ⟨A, hA, hcov⟩ := LiZhongQC.s30a_exists_covers hp α
  have hcovInv := covers_reverse hcov
  have htr : LiZhongQC.slTrace A⁻¹ = LiZhongQC.slTrace A := by
    simpa only [LiZhongQC.slTrace, Matrix.trace_fin_two] using
      Hyperbolic.hSL_trace_inverse A
  by_cases hh : LiZhongQC.IsHyperbolic A
  · have hhi : LiZhongQC.IsHyperbolic A⁻¹ := by
      simpa only [LiZhongQC.IsHyperbolic, htr] using hh
    rw [LiZhongQC.s30a_len_hyp hp (Γ.inv_mem hA) hhi hcovInv,
      LiZhongQC.s30a_len_hyp hp hA hh hcov]
    unfold LiZhongQC.translationLength
    rw [htr]
  · have hhi : ¬ LiZhongQC.IsHyperbolic A⁻¹ := by
      simpa only [LiZhongQC.IsHyperbolic, htr] using hh
    have hzero := (LiZhongQC.s30a_classify hp (LiZhongQC.s27g_actsFreely hp) hA hcov).resolve_right
      (fun h => hh h.1)
    have hzeroInv := (LiZhongQC.s30a_classify hp (LiZhongQC.s27g_actsFreely hp)
      (Γ.inv_mem hA) hcovInv).resolve_right (fun h => hhi h.1)
    exact hzeroInv.1.trans hzero.1.symm

/-- On every original marked quotient point, reversing the source loop preserves length. -/
theorem markedGeodesicLength_reverse {X : Type} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (α : LiZhongQC.Loop X) (t : TeichmullerSpace.{0, 0} R) :
    markedGeodesicLength R hg hgenus ⟨α.1, α.2.symm⟩ t =
      markedGeodesicLength R hg hgenus α t := by
  refine Quotient.inductionOn t ?_
  intro m
  let := m.surface.toRiemannAtlas.toChartedSpace
  let M := m.geodesicLengthModel R hg hgenus
  obtain ⟨Γ, _, hp⟩ := M.exists_halfPlaneCover_uniformization
  have hrev := freeHomotopyLength_reverse hp
    ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩
  change (LiZhongQC.freeHomotopyLength M.halfPlaneCover
      ⟨m.markingMap α.1, α.2.symm.map m.markingMap.continuous⟩).toReal =
    (LiZhongQC.freeHomotopyLength M.halfPlaneCover
      ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩).toReal
  simpa only [Path.map_symm] using congrArg ENNReal.toReal hrev

end LowDimensionalTopology.Geometry.Teichmuller
