module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.QuotientMetric

/-!
# Local changes between actual inverse covering sheets

Two inverse sheets of the original analytic disk covering differ locally by a
normalized disk Möbius transformation. The transformation is anchored at the two
inverse images of the chosen surface point; its global covering identity and
local injectivity of the second sheet then identify the actual inverse branches.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Hyperbolic Auxiliary.Analysis

variable {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}

/-- Actual inverse sheets of the same original disk covering differ near any
common target point by one normalized disk Möbius map. -/
theorem discCoverSheets_eventually_related_normalized (M : HyperbolicSurfaceModel R)
    (l k : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (hk : M.discCover = (k : extendedUnitDisc → X))
    (x : X) (hxl : x ∈ l.target) (hxk : x ∈ k.target) :
    ∃ (u c : ℂ) (_hdet : Complex.normSq u - Complex.normSq c = 1),
      ∀ᶠ y in 𝓝 x, discFiniteChart (k.symm y) =
        discFractionalMap u c (discFiniteChart (l.symm y)) := by
  let a := discFiniteHomeomorph (l.symm x)
  let b := discFiniteHomeomorph (k.symm x)
  have hpl : M.discCover (l.symm x) = x := by
    rw [hl]
    exact l.right_inv hxl
  have hpk : M.discCover (k.symm x) = x := by
    rw [hk]
    exact k.right_inv hxk
  have hab : M.discCover (discFiniteHomeomorph.symm a) =
      M.discCover (discFiniteHomeomorph.symm b) := by
    simpa only [a, b, Homeomorph.symm_apply_apply] using hpl.trans hpk.symm
  obtain ⟨u, c, hdet, hstart, hchange⟩ := analytic_discCovers_exists_normalized
    R.toRiemannAtlas M.discCover M.discCover M.discCover_covering
    M.discCover_covering M.discCover_analytic M.discCover_analytic a b hab
  let E := discFractionalHomeomorph u c hdet
  let H : X → extendedUnitDisc := fun y =>
    discFiniteHomeomorph.symm (E (discFiniteHomeomorph (l.symm y)))
  have hHx : H x = k.symm x := by
    change discFiniteHomeomorph.symm (discFractionalHomeomorph u c hdet a) = k.symm x
    rw [hstart]
    exact discFiniteHomeomorph.symm_apply_apply (k.symm x)
  have hHcont : ContinuousAt H x :=
    discFiniteHomeomorph.symm.continuous.continuousAt.comp
      (E.continuous.continuousAt.comp
        (discFiniteHomeomorph.continuous.continuousAt.comp (l.continuousAt_symm hxl)))
  have hHmem : ∀ᶠ y in 𝓝 x, H y ∈ k.source := by
    apply hHcont.eventually_mem
    rw [hHx]
    exact k.open_source.mem_nhds (k.map_target hxk)
  refine ⟨u, c, hdet, ?_⟩
  filter_upwards [l.open_target.mem_nhds hxl, hHmem] with y hyl hyH
  have hproj : k (H y) = y := by
    calc
      k (H y) = M.discCover (H y) := (congrFun hk (H y)).symm
      _ = M.discCover (l.symm y) := by
        simpa only [H, E, Homeomorph.symm_apply_apply] using
          hchange (discFiniteHomeomorph (l.symm y))
      _ = l (l.symm y) := congrFun hl (l.symm y)
      _ = y := l.right_inv hyl
  have hbranch : k.symm y = H y :=
    (congrArg k.symm hproj).symm.trans (k.left_inv hyH)
  have hnative : discFiniteHomeomorph (k.symm y) =
      E (discFiniteHomeomorph (l.symm y)) :=
    (congrArg discFiniteHomeomorph hbranch).trans (discFiniteHomeomorph.apply_symm_apply _)
  change (discFiniteHomeomorph (k.symm y) : ℂ) =
    (E (discFiniteHomeomorph (l.symm y)) : ℂ)
  exact congrArg ((↑) : Complex.UnitDisc → ℂ) hnative

end LowDimensionalTopology.Geometry.Teichmuller
