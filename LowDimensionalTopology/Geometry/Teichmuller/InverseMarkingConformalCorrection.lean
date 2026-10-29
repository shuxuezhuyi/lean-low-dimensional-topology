module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCClosedCompatibility

/-!
# Inverse markings with their conformal correction

Equality of two markings with the same target supplies a biholomorphic target
map. On taking inverse markings this map is retained as a precomposition.
The proof only composes the given marking homotopy with the two inverse maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
open Surfaces

/-- Equal classes on a closed reference give equal inverse classes after
precomposing the second inverse marking by the actual conformal target factor. -/
theorem exists_inverse_marking_conformal_correction
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y) (f g : X ≃ₜ Y) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := S.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := S.toRiemannAtlas.isManifold
    ∀ (hf : LiZhongQC.IsQCRS f) (hg : LiZhongQC.IsQCRS g),
      let mf : ClosedMarked R :=
        ⟨Surface.ofRiemannSurface S.toRiemannSurface, f, hf⟩
      let mg : ClosedMarked R :=
        ⟨Surface.ofRiemannSurface S.toRiemannSurface, g, hg⟩
      mk mf = mk mg →
      ∃ (h : Y ≃ₜ Y) (hh : LiZhongQC.IsBiholomorphic (h : Y → Y)),
        mk ({
          target := Surface.ofRiemannSurface R.toRiemannSurface,
          marking := f.symm, qc := LiZhongQC.s28q_isQCRS_symm hf } : ClosedMarked S) =
        mk ({
          target := Surface.ofRiemannSurface R.toRiemannSurface,
          marking := h.trans g.symm,
          qc := LiZhongQC.s28q_isQCRS_trans
            ⟨1, (LiZhongQC.isKQCRS_one_iff h).mpr hh⟩
            (LiZhongQC.s28q_isQCRS_symm hg) } : ClosedMarked S) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  intro hf hg
  dsimp only
  intro heq
  obtain ⟨h, hh, hfg⟩ := Quotient.exact heq
  change ContinuousMap.Homotopic
    (⟨f.trans h, (f.trans h).continuous⟩ : C(X, Y)) (g : C(X, Y)) at hfg
  refine ⟨h, hh, ?_⟩
  apply Quotient.sound
  refine ⟨Homeomorph.refl X, LiZhongQC.isBiholomorphic_id, ?_⟩
  change ContinuousMap.Homotopic
    (f.symm : C(Y, X)) (⟨h.trans g.symm, (h.trans g.symm).continuous⟩ : C(Y, X))
  have H := (ContinuousMap.Homotopic.refl (g.symm : C(Y, X))).comp
    (hfg.comp (ContinuousMap.Homotopic.refl (f.symm : C(Y, X))))
  have hleft : (g.symm : C(Y, X)).comp
      ((⟨f.trans h, (f.trans h).continuous⟩ : C(X, Y)).comp (f.symm : C(Y, X))) =
      (⟨h.trans g.symm, (h.trans g.symm).continuous⟩ : C(Y, X)) := by
    ext y
    exact congrArg (fun z => g.symm (h z)) (f.apply_symm_apply y)
  have hright : (g.symm : C(Y, X)).comp
      ((g : C(X, Y)).comp (f.symm : C(Y, X))) = (f.symm : C(Y, X)) := by
    ext y
    exact g.symm_apply_apply (f.symm y)
  rw [hleft, hright] at H
  exact H.symm

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
