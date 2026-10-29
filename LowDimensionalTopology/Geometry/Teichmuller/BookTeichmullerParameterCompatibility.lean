module

public import LowDimensionalTopology.Geometry.Teichmuller.BookTeichmullerMaps
public import LowDimensionalTopology.Geometry.Teichmuller.TeichmullerL1Parameters

/-!
# The specific L1 parameter map and every book-defined QC representative

Any actual QC map with the normalized book coefficient represents exactly the
class assigned by the actual L1 parameter map. The target carrier and complex
atlas are retained, and the comparison uses the same-Beltrami conformal map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u

/-- The specific native L1 parameter map agrees with every actual QC
representative of the book-defined Teichmüller map for the same differential. -/
theorem bookCoefficient_parameterClass
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (φ : ↥(QuadraticL1.openUnitBall R)) (f : X ≃ₜ Y)
    (hf :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f)
    (hμ : HasBookTeichmullerCoefficient R S f φ.val) :
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    TeichmullerSpace.toSource R (TeichmullerSpace.l1ParameterMap R hg hgenus φ) =
      Quot.mk _ (⟨S.toSourceClosedRS, f, hf⟩ : LiZhongQC.MarkedRS X) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  let := R.t2Space
  let := S.t2Space
  let := R.connectedSpace
  let := S.connectedSpace
  let := R.compactSpace
  let := S.compactSpace
  by_cases hz : φ.val = 0
  · have ha : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f := by
      rcases bookCoefficient_geometric R S φ.val φ.property f hf hμ with
        ⟨_, ha⟩ | ⟨q', hT⟩
      · exact ha
      · exact False.elim (hT.initial_ne (by simp only [hz, Submodule.coe_zero]))
    have hb := (analyticHomeomorph_iff_sourceBiholomorphic
      R.toRiemannAtlas S.toRiemannAtlas f).mp ha
    have hbase := TeichmullerSpace.l1ParameterMap_zero R hg hgenus φ hz
    exact (congrArg (TeichmullerSpace.toSource R) hbase).trans (by
      apply Quot.sound
      refine ⟨f, hb, ?_⟩
      change ContinuousMap.Homotopic (f : C(X, Y)) (f : C(X, Y))
      exact ContinuousMap.Homotopic.refl _)
  · have hp := TeichmullerSpace.l1ParameterMap_deformation R hg hgenus φ hz
    obtain ⟨D, e, hqc, q', hDef, he⟩ := hp
    have hT := LiZhongQC.teichDeformation_isTeichmullerMap hDef
    have hk0 : 0 ≤ QuadraticL1.bookNorm R φ.val := by
      unfold QuadraticL1.bookNorm
      positivity
    have hk1 := (QuadraticL1.mem_openUnitBall R φ.val).mp φ.property
    have hBel := LiZhongQC.teichmullerBeltrami_isBeltramiDifferential φ.val.property hk0 hk1
    have hc := sameBeltrami_biholomorphic hT.qc hf hk1 hBel
      (LiZhongQC.teichmullerMap_beltrami hT).1 hμ
    have hclass :
        Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X)) (⟨D, e, hqc⟩ : LiZhongQC.MarkedRS X) =
          Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := X))
            (⟨S.toSourceClosedRS, f, hf⟩ : LiZhongQC.MarkedRS X) := by
      apply Quot.sound
      refine ⟨e.symm.trans f, hc, ?_⟩
      have hcomp : e.trans (e.symm.trans f) = f := by
        ext x
        simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
      change ContinuousMap.Homotopic
        ((e.trans (e.symm.trans f) : X ≃ₜ Y) : C(X, Y)) (f : C(X, Y))
      rw [hcomp]
    exact he.trans hclass

end LowDimensionalTopology.Geometry.Teichmuller
