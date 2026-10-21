/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianLimitSets
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.Closed
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
@[expose] public section
open Set Filter
open scoped Topology OnePoint Complex.UnitDisc UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- A true invariant nonempty subset has every actual limit point in its ambient closure. -/
theorem nielsen_limitSet_subset_closure
    (H : Subgroup Mobius.complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H)
    (S : Set Mobius.ExtendedComplex) (hne : S.Nonempty)
    (hi : ∀g : H,∀p∈S,g • p∈S) : DiscreteGroups.mobiusLimitSet H⊆closure S := by
  apply DiscreteGroups.mobiusLimitSet_minimal H hH (closure S) isClosed_closure (hne.mono subset_closure)
  intro g p hp
  have hg : g.val.val '' S⊆S:=by rintro _ ⟨z,hz,rfl⟩;exact hi g z hz
  exact closure_mono hg (image_closure_subset_closure_image (Mobius.complexMobiusContinuousMap g.val).continuous
    ⟨p,hp,rfl⟩)

/-- Interior of an actual convex hull is contained in every open convex set with the prescribed closure data. -/
theorem nielsen_interior_convexHull_subset {A S : Set ℂ} (hconv : Convex ℝ S)
    (hopen : IsOpen S) (hne : S.Nonempty) (hA : A⊆closure S) : interior (convexHull ℝ A)⊆S := by
  have hneI : (interior S).Nonempty:=hopen.interior_eq.symm ▸ hne
  have hsubset:=interior_mono (convexHull_min hA hconv.closure)
  rw [hconv.interior_closure_eq_interior_of_nonempty_interior hneI,hopen.interior_eq] at hsubset
  exact hsubset

/-- A convex set whose closure contains the whole ideal circle already contains the entire open disc. -/
theorem nielsen_ball_subset_of_sphere_subset_closure {S : Set ℂ} (hconv : Convex ℝ S)
    (hcircle : Metric.sphere (0 : ℂ) 1⊆closure S) : Metric.ball (0 : ℂ) 1⊆S := by
  have hclosed : Metric.closedBall (0 : ℂ) 1⊆closure S:=by
    rw [←convexHull_sphere_eq_closedBall (0 : ℂ) (by norm_num : (0 : ℝ)≤1)]
    exact convexHull_min hcircle hconv.closure
  have hspanclosed : closure S⊆(affineSpan ℝ S : Set ℂ):=
    closure_minimal (subset_affineSpan ℝ S) (affineSpan ℝ S).closed_of_finiteDimensional
  have hballspan : Metric.ball (0 : ℂ) 1⊆(affineSpan ℝ S : Set ℂ):=
    Metric.ball_subset_closedBall.trans (hclosed.trans hspanclosed)
  have hspan : affineSpan ℝ S=⊤:=by
    have hle : affineSpan ℝ (Metric.ball (0 : ℂ) 1)≤affineSpan ℝ S:=affineSpan_le.mpr hballspan
    rw [Metric.isOpen_ball.affineSpan_eq_top (Metric.nonempty_ball.mpr (by norm_num))] at hle
    exact top_unique hle
  have hneI : (interior S).Nonempty:=hconv.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  have hballInterior : Metric.ball (0 : ℂ) 1⊆interior (closure S):=
    Metric.isOpen_ball.subset_interior_iff.mpr (Metric.ball_subset_closedBall.trans hclosed)
  rw [hconv.interior_closure_eq_interior_of_nonempty_interior hneI] at hballInterior
  exact hballInterior.trans interior_subset

/-- Klein coordinates have a continuous formula on the whole complex plane. -/
theorem nielsen_continuous_kleinFormula : Continuous Hyperbolic.kleinFormula := by
  have hs : Continuous (fun z : ℂ=>(2 : ℝ)/(1+‖z‖^2)):=
    continuous_const.div (continuous_const.add (continuous_norm.pow 2)) (fun _=>by positivity)
  exact (Complex.continuous_ofReal.comp hs).mul continuous_id

theorem nielsen_kleinFormula_ideal
    (z : ℂ)
    (hz : ‖z‖=1) : Hyperbolic.kleinFormula z=z := by
  norm_num [Hyperbolic.kleinFormula,hz]

/-- Actual Euclidean ideal limits remain unchanged under the continuous Klein extension. -/
theorem nielsen_klein_closure_ideal {S : Set 𝔻} {p : ℂ} (hp : ‖p‖=1)
    (hcl : p∈closure (((↑) : 𝔻 → ℂ) '' S)) : p∈closure (Hyperbolic.kleinCoordinate '' S) := by
  have h:=image_closure_subset_closure_image nielsen_continuous_kleinFormula ⟨p,hcl,rfl⟩
  rw [nielsen_kleinFormula_ideal p hp] at h
  have himg : Hyperbolic.kleinFormula '' (((↑) : 𝔻 → ℂ) '' S)=Hyperbolic.kleinCoordinate '' S:=by
    rw [Set.image_image]
    rfl
  rw [himg] at h
  exact h


/-- Filling the true ideal boundary forces an actual hyperbolically convex set to fill D. -/
theorem nielsen_discHConvex_eq_univ_of_boundary_closure
    (S : Set 𝔻)
    (hconv : Hyperbolic.DiscHConvex S)
    (hboundary : Hyperbolic.extendedDiscIdealBoundary⊆closure (Hyperbolic.extendedDiscPoint '' S)) : S=univ := by
  have hcircle : Metric.sphere (0 : ℂ) 1⊆closure (Hyperbolic.kleinCoordinate '' S):=by
    intro p hp
    have hpNorm : ‖p‖=1:=by simpa only [Metric.mem_sphere,dist_zero_right] using hp
    apply nielsen_klein_closure_ideal hpNorm
    have hpB : (p : Mobius.ExtendedComplex)∈Hyperbolic.extendedDiscIdealBoundary:=by
      exact ⟨p,by simpa only [Metric.mem_sphere,dist_zero_right] using hpNorm,rfl⟩
    have hpc:=hboundary hpB
    have himg : ((↑) : ℂ → Mobius.ExtendedComplex) '' (((↑) : 𝔻 → ℂ) '' S)=Hyperbolic.extendedDiscPoint '' S:=by
      rw [Set.image_image]
      rfl
    rw [←himg] at hpc
    change p∈((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' closure (((↑) : ℂ → Mobius.ExtendedComplex) '' (((↑) : 𝔻 → ℂ) ''
      S)) at hpc
    rw [Hyperbolic.onePoint_coe_preimage_closure_image] at hpc
    exact hpc
  have hb:=nielsen_ball_subset_of_sphere_subset_closure ((Hyperbolic.discHConvex_iff_klein_convex S).mp hconv) hcircle
  apply eq_univ_of_forall
  intro z
  have hz : Hyperbolic.kleinCoordinate z∈Hyperbolic.kleinCoordinate '' S:=hb (by
    exact mem_ball_zero_iff.mpr (Hyperbolic.poincareToKlein z).norm_lt_one)
  exact Hyperbolic.kleinCoordinate_injective.mem_set_image.mp hz


/-- The first-kind assertion uses genuine sphere limit points and actual native hyperbolic convexity. -/
theorem nielsen_firstKind_convex_eq_univ
    (H : Subgroup Mobius.complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H)
    (hfirst : DiscreteGroups.mobiusLimitSet H=Hyperbolic.extendedDiscIdealBoundary) (S : Set 𝔻)
    (hne : S.Nonempty) (hconv : Hyperbolic.DiscHConvex S)
    (hi : ∀g : H,∀p∈Hyperbolic.extendedDiscPoint '' S,g • p∈Hyperbolic.extendedDiscPoint '' S) : S=univ := by
  apply nielsen_discHConvex_eq_univ_of_boundary_closure S hconv
  rw [←hfirst]
  exact nielsen_limitSet_subset_closure H hH _ (hne.image _) hi

/-- The same boundary-closure argument holds in the genuine half-plane via the actual Cayley homeomorphism. -/
theorem nielsen_hConvex_eq_univ_of_boundary_closure
    (S : Set ℍ)
    (hconv : Hyperbolic.HConvex S)
    (hboundary : Hyperbolic.halfPlaneIdealBoundary⊆closure (Hyperbolic.extendedHalfPlanePoint '' S)) : S=univ := by
  have hdisc : Hyperbolic.halfPlaneToDisc '' S=univ:=by
    apply nielsen_discHConvex_eq_univ_of_boundary_closure _ ((Hyperbolic.hConvex_iff_cayley_discHConvex S).mp hconv)
    rw [←Hyperbolic.extendedCayley_image_idealBoundary]
    rintro p ⟨q,hq,rfl⟩
    have hp:=image_closure_subset_closure_image Hyperbolic.extendedCayley.continuous ⟨q,hboundary hq,rfl⟩
    have himg : Hyperbolic.extendedCayley '' (Hyperbolic.extendedHalfPlanePoint '' S)=Hyperbolic.extendedDiscPoint '' (Hyperbolic.halfPlaneToDisc '' S):=by
      rw [Set.image_image,Set.image_image]
      congr 1
      funext z
      exact Hyperbolic.extendedCayley_halfPlane z
    rw [himg] at hp
    exact hp
  apply eq_univ_of_forall
  intro z
  have hz : Hyperbolic.halfPlaneToDisc z∈Hyperbolic.halfPlaneToDisc '' S:=hdisc.symm ▸ mem_univ _
  exact Hyperbolic.cayleyEquiv.injective.mem_set_image.mp hz

/-- The first-kind convexity result in the true half-plane model, with no openness assumption. -/
theorem nielsen_firstKind_hConvex_eq_univ
    (H : Subgroup Mobius.complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H)
    (hfirst : DiscreteGroups.mobiusLimitSet H=Hyperbolic.halfPlaneIdealBoundary) (S : Set ℍ)
    (hne : S.Nonempty) (hconv : Hyperbolic.HConvex S)
    (hi : ∀g : H,∀p∈Hyperbolic.extendedHalfPlanePoint '' S,g • p∈Hyperbolic.extendedHalfPlanePoint '' S) : S=univ := by
  apply nielsen_hConvex_eq_univ_of_boundary_closure S hconv
  rw [←hfirst]
  exact nielsen_limitSet_subset_closure H hH _ (hne.image _) hi

/-- First kind in the original Fuchsian definition implies actual non-elementarity. -/
theorem FuchsianDisc.firstKind_nonElementary
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hfirst : D.IsFirstKind) : DiscreteGroups.IsNonElementary H := by
  intro hE
  exact (ne_of_ssubset (D.elementary_isSecondKind hE)) hfirst


theorem nielsen_unitDisc_frontier : frontier Hyperbolic.extendedUnitDisc=Hyperbolic.extendedDiscIdealBoundary := by
  rw [Mobius.frontier_extendedUnitDisc_eq_circle]
  ext p
  induction p using OnePoint.rec with
  | infty=>simp [Hyperbolic.extendedDiscIdealBoundary]
  | coe z=>simp [Hyperbolic.coe_mem_extendedDiscIdealBoundary]

theorem nielsen_openHalfPlane_frontier : frontier Hyperbolic.openHalfPlaneSet=Hyperbolic.halfPlaneIdealBoundary := by
  have he : Hyperbolic.extendedOpenDisc=Hyperbolic.extendedUnitDisc:=by
    ext p
    induction p using OnePoint.rec with
    | infty=>simp [Hyperbolic.extendedOpenDisc,Hyperbolic.extendedUnitDisc]
    | coe z=>simp [Hyperbolic.extendedOpenDisc,Hyperbolic.extendedUnitDisc,Metric.mem_ball,dist_zero_right]
  apply Hyperbolic.extendedCayley.injective.image_injective
  rw [Homeomorph.image_frontier,Hyperbolic.extendedCayley_image_openHalfPlane,Hyperbolic.extendedCayley_image_idealBoundary,
    he,nielsen_unitDisc_frontier]

/-- The original first-kind source statement in D, deriving rather than assuming non-elementarity. -/
theorem FuchsianDisc.firstKind_discHConvex_eq_univ
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hfirst : D.IsFirstKind)
    (S : Set 𝔻) (hne : S.Nonempty) (hconv : Hyperbolic.DiscHConvex S)
    (hi : ∀g : H,∀p∈Hyperbolic.extendedDiscPoint '' S,g • p∈Hyperbolic.extendedDiscPoint '' S) : S=univ := by
  have hH:=D.firstKind_nonElementary hfirst
  have hf : fuchsianLimitSet H=frontier D.carrier:=hfirst
  apply nielsen_firstKind_convex_eq_univ H hH _ S hne hconv hi
  rw [←fuchsianLimitSet_eq_nonElementary H hH,hf,hD,nielsen_unitDisc_frontier]

/-- The original first-kind source statement in H, with the genuine closed-segment convexity. -/
theorem FuchsianDisc.firstKind_hConvex_eq_univ
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.openHalfPlaneSet)
    (hfirst : D.IsFirstKind)
    (S : Set ℍ) (hne : S.Nonempty) (hconv : Hyperbolic.HConvex S)
    (hi : ∀g : H,∀p∈Hyperbolic.extendedHalfPlanePoint '' S,g • p∈Hyperbolic.extendedHalfPlanePoint '' S) : S=univ := by
  have hH:=D.firstKind_nonElementary hfirst
  have hf : fuchsianLimitSet H=frontier D.carrier:=hfirst
  apply nielsen_firstKind_hConvex_eq_univ H hH _ S hne hconv hi
  rw [←fuchsianLimitSet_eq_nonElementary H hH,hf,hD,nielsen_openHalfPlane_frontier]

end
end LowDimensionalTopology.Geometry.Fuchsian
