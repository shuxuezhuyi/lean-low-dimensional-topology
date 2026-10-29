module

public import LowDimensionalTopology.Unproved.Surfaces.SimpleClosedGeodesicRepresentatives
public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleClassHomeomorph
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalWolpert
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedLengthSpectrum

/-!
# Simple image representatives and Wolpert's length bound

Freely homotopic original closed geodesics have the same full-period length.
A simple representative in the image class therefore satisfies Wolpert's
upper bound with the same quasiconformal constant.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry.Teichmuller

/-- A simple image representative retains the genuine Wolpert upper bound,
for the original actual K-QC map and the whole original geodesic period. -/
theorem EssentialSimpleCircle.exists_simple_wolpert_image
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (hSimple : LowDimensionalTopology.Unproved.Surfaces.SimpleClosedGeodesicRepresentatives R g M)
    (c : EssentialSimpleCircle X) (q : OriginalClosedGeodesic M)
    (hq : LiZhongQC.FreelyHomotopic (circleRepresentativeLoop c.val) q.toLoop)
    (f : X ≃ₜ X) {K : ℝ}
    (hf : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsKQCRS f K) :
    ∃ r : OriginalClosedGeodesic M,
      LiZhongQC.FreelyHomotopic
          (circleRepresentativeLoop (c.mapHomeomorph f).val) r.toLoop ∧
        Function.Injective (r.periodic.lift : AddCircle (1 : ℝ) → X) ∧
          r.length.toReal ≤ K * q.length.toReal := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.compactSpace
  obtain ⟨s, hfs, _hlower, hupper⟩ := q.exists_wolpert_image M f hf
  obtain ⟨r, hr, hri⟩ := hSimple hg hgenus (c.mapHomeomorph f)
  have hrs : LiZhongQC.FreelyHomotopic r.toLoop s.toLoop := by
    change LiZhongQC.FreelyHomotopic
      ⟨f (circleRepresentativeLoop c.val).1,
        (circleRepresentativeLoop c.val).2.map f.continuous⟩ r.toLoop at hr
    exact LiZhongQC.s30b_fh_trans (LiZhongQC.s30b_fh_symm hr)
      (LiZhongQC.s30b_fh_trans (LiZhongQC.s30b_fh_map f.continuous hq) hfs)
  have hlength : r.length = s.length :=
    r.length_eq_freeHomotopyLength.trans
      ((LiZhongQC.s30b_fhl_congr M.halfPlaneCover hrs).trans
        s.length_eq_freeHomotopyLength.symm)
  refine ⟨r, hr, hri, ?_⟩
  rw [hlength]
  exact hupper

end LowDimensionalTopology.Geometry.Surfaces
