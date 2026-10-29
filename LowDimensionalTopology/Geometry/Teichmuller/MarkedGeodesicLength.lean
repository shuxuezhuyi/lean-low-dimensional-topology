module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedLengthSpectrum

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

/-- Biholomorphic changes of the original target preserve free-class length;
the real Möbius lift is derived from the actual analytic atlases. -/
theorem freeLength_eq_of_analyticHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (R : RiemannSurface X) (S : RiemannSurface Y)
    (M : HyperbolicSurfaceModel R) (N : HyperbolicSurfaceModel S)
    (f : X ≃ₜ Y) (hf : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f)
    (α : LiZhongQC.Loop X) :
    LiZhongQC.freeHomotopyLength N.halfPlaneCover ⟨f α.1, α.2.map f.continuous⟩ =
      LiZhongQC.freeHomotopyLength M.halfPlaneCover α := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  let := R.t2Space
  let := S.t2Space
  let := R.connectedSpace
  let := S.connectedSpace
  obtain ⟨Γ, _, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨Δ, _, hq⟩ := N.exists_halfPlaneCover_uniformization
  obtain ⟨b, hb⟩ := N.halfPlaneCover_surjective (f (M.halfPlaneCover UpperHalfPlane.I))
  obtain ⟨F, hF, _⟩ := LiZhongQC.exists_lift hp hq f UpperHalfPlane.I b hb
  have hf1 := (LiZhongQC.isKQCRS_one_iff f).mpr
    ((analyticHomeomorph_iff_sourceBiholomorphic R.toRiemannAtlas S.toRiemannAtlas f).mp hf)
  obtain ⟨A, hA⟩ := LiZhongQC.utm_eq_smul_of_isKQC_one F
    (LiZhongQC.h23l_lift_isKQC hp hq hf1 hF)
  exact LiZhongQC.s30b_fhl_eq_of_mob f A (fun z => by rw [← hA z]; exact hF z) α

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)

/-- Choose an actual hyperbolic model on the unchanged marked target;
the original genus transports along that target's genuine marking. -/
def MarkedRiemannSurface.geodesicLengthModel (m : MarkedRiemannSurface.{0, 0} R) :
    HyperbolicSurfaceModel m.surface.toRiemannSurface :=
  (m.surface.hyperbolicOfGenusGeTwo hg (by
    obtain ⟨e⟩ := hgenus
    exact ⟨m.marking.toHomeomorph.symm.trans e⟩)).model

/-- The full free-homotopy length of a source loop transported by the actual
marking, measured on that same target's hyperbolic model. -/
def markedLoopLength (α : LiZhongQC.Loop X) (m : MarkedRiemannSurface.{0, 0} R) : ENNReal :=
  LiZhongQC.freeHomotopyLength (m.geodesicLengthModel R hg hgenus).halfPlaneCover
    ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩

/-- Every source loop has finite free-class length on every actual marked target;
the bound comes from its actual covering element, without a geodesic premise. -/
theorem markedLoopLength_ne_top (α : LiZhongQC.Loop X) (m : MarkedRiemannSurface.{0, 0} R) :
    markedLoopLength R hg hgenus α m ≠ ⊤ := by
  let := m.surface.toRiemannAtlas.toChartedSpace
  let M := m.geodesicLengthModel R hg hgenus
  obtain ⟨Γ, _, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨A, hA, hcov⟩ := LiZhongQC.s30a_exists_covers hp
    ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (LiZhongQC.s30a_ub hp hA hcov UpperHalfPlane.I)

/-- The original biholomorphic target equivalence and its actual marking
homotopy preserve the transported loop's entire free-class length. -/
theorem markedLoopLength_congr (α : LiZhongQC.Loop X)
    {m n : MarkedRiemannSurface.{0, 0} R} (hmn : MarkedRiemannSurface.Equivalent m n) :
    markedLoopLength R hg hgenus α m = markedLoopLength R hg hgenus α n := by
  obtain ⟨f, hf, hhom⟩ := hmn
  have he := freeLength_eq_of_analyticHomeomorph _ _
    (m.geodesicLengthModel R hg hgenus) (n.geodesicLengthModel R hg hgenus) f hf
    ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩
  exact he.symm.trans (LiZhongQC.s30b_fhl_congr _ (LiZhongQC.s30b_fh_of_homotopic hhom α))

/-- The length function on the entire native marked quotient. For one traversal
of an essential simple pants curve this is its marked geodesic length function. -/
def markedGeodesicLength (α : LiZhongQC.Loop X) : TeichmullerSpace.{0, 0} R → ℝ :=
  Quotient.lift (fun m => (markedLoopLength R hg hgenus α m).toReal)
    (fun _ _ h => congrArg ENNReal.toReal (markedLoopLength_congr R hg hgenus α h))

/-- On any genuine model of the same marked target, the quotient value is the
actual full-period length of any original geodesic in the transported free class. -/
theorem markedGeodesicLength_mk_eq (α : LiZhongQC.Loop X)
    (m : MarkedRiemannSurface.{0, 0} R) (M : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (q : OriginalClosedGeodesic M)
    (hq : LiZhongQC.FreelyHomotopic
      ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ q.toLoop) :
    markedGeodesicLength R hg hgenus α (TeichmullerSpace.mk m) = q.length.toReal := by
  let := m.surface.compactSpace
  have hi := freeLength_eq_of_analyticHomeomorph _ _ (m.geodesicLengthModel R hg hgenus) M
    (Homeomorph.refl _) (RiemannAnalyticMap.id _)
    ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩
  exact congrArg ENNReal.toReal ((hi.symm.trans (LiZhongQC.s30b_fhl_congr _ hq)).trans
    q.length_eq_freeHomotopyLength.symm)

end LowDimensionalTopology.Geometry.Teichmuller
