module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceChange

/-!
# The same marked length under an actual reference change

The reference loop is carried by the given quasiconformal homeomorphism.
The target and the transported free homotopy class are unchanged, so the
actual length on the original native marked quotient has the same value.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

/-- Precomposing the actual marking by the inverse reference map leaves the
full free-class length of the corresponding loop unchanged. -/
theorem markedGeodesicLength_referenceChangeEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    {g : ℕ} (hg : 1 < g) (hR : R.HasGenus g) (hS : S.HasGenus g)
    (e : X ≃ₜ Y)
    (he : letI := R.toRiemannAtlas.toChartedSpace
      letI := S.toRiemannAtlas.toChartedSpace; LiZhongQC.IsQCRS e)
    (α : LiZhongQC.Loop X) (a : TeichmullerSpace R) :
    markedGeodesicLength S (Nat.succ_le_of_lt hg) hS
        ⟨e α.1, α.2.map e.continuous⟩
        (referenceChangeEquiv R S hg hR hS e he a) =
      markedGeodesicLength R (Nat.succ_le_of_lt hg) hR α a := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  refine Quotient.inductionOn a ?_
  intro m
  let n := Quotient.out (referenceChangeEquiv R S hg hR hS e he (mk m))
  have hn : mk n = referenceChangeEquiv R S hg hR hS e he (mk m) :=
    Quotient.out_eq _
  have hclass :
      Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := Y))
          (SourceReferenceChange.marked e he m.toSource) =
        Quot.mk (LiZhongQC.MarkedRS.Equiv (S₀ := Y)) n.toSource := by
    calc
      _ = SourceReferenceChange.quotientMap e he (toSource R (mk m)) := rfl
      _ = toSource S (referenceChangeEquiv R S hg hR hS e he (mk m)) :=
        (toSource_referenceChangeEquiv R S hg hR hS e he (mk m)).symm
      _ = _ := congrArg (toSource S) hn.symm
  obtain ⟨f, hf, hhom⟩ :=
    (LiZhongQC.markedRS_equiv_equivalence (S₀ := Y)).eqvGen_iff.mp
      (Quot.eqvGen_exact hclass)
  have hanalytic : RiemannAnalyticMap m.surface.toRiemannAtlas
      n.surface.toRiemannAtlas f :=
    (analyticHomeomorph_iff_sourceBiholomorphic
      m.surface.toRiemannAtlas n.surface.toRiemannAtlas f).mpr hf
  change ContinuousMap.Homotopic
    ((_root_.toContinuousMap f).comp
      (m.markingMap.comp (_root_.toContinuousMap e.symm))) n.markingMap at hhom
  have htransport := hhom.comp
    (ContinuousMap.Homotopic.refl (_root_.toContinuousMap e))
  have hcancel :
      ((_root_.toContinuousMap f).comp
        (m.markingMap.comp (_root_.toContinuousMap e.symm))).comp
          (_root_.toContinuousMap e) =
        (_root_.toContinuousMap f).comp m.markingMap := by
    ext x
    exact congrArg (fun z => f (m.markingMap z)) (e.symm_apply_apply x)
  rw [hcancel] at htransport
  have hfree := LiZhongQC.s30b_fh_of_homotopic htransport α
  have hanalytic := freeLength_eq_of_analyticHomeomorph _ _
    (m.geodesicLengthModel R (Nat.succ_le_of_lt hg) hR)
    (n.geodesicLengthModel S (Nat.succ_le_of_lt hg) hS) f hanalytic
    ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩
  have hlength : markedLoopLength R (Nat.succ_le_of_lt hg) hR α m =
      markedLoopLength S (Nat.succ_le_of_lt hg) hS
        ⟨e α.1, α.2.map e.continuous⟩ n :=
    hanalytic.symm.trans (LiZhongQC.s30b_fhl_congr _ hfree)
  change markedGeodesicLength S (Nat.succ_le_of_lt hg) hS
      ⟨e α.1, α.2.map e.continuous⟩ (referenceChangeEquiv R S hg hR hS e he (mk m)) =
    markedGeodesicLength R (Nat.succ_le_of_lt hg) hR α (mk m)
  rw [← hn]
  exact congrArg ENNReal.toReal hlength.symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
