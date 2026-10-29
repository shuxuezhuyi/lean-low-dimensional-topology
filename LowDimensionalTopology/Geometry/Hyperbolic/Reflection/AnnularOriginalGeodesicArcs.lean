module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairCayleyOrbitTransport
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularSixFeetProjectionInjective
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalGeodesicArcs
public import Mathlib.Topology.UnitInterval

/-!
# Actual finite original geodesic arcs between the annular six feet

The same annular quotient model, mirrors and six feet give three finite
embedded arcs. Their entire traces are the projected closed native segments,
their endpoints are the literal projections, and their lengths are the
actual native foot-to-foot distances.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- Distinct native endpoints and finite projection injectivity produce the
same original finite geodesic arc, with its full segment trace and length. -/
theorem HyperbolicSurfaceModel.exists_original_geodesic_c1_arc_between
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (z w : ℍ) (hzw : z ≠ w)
    (hinj : InjOn M.halfPlaneCover (closedHSegment z w)) :
    ∃ (c : HyperbolicSurfaceC1CurvePiece M)
      (p : Path (M.halfPlaneCover z) (M.halfPlaneCover w)),
      (∀ t : I, p t = c.curve t) ∧
      range p = M.halfPlaneCover '' closedHSegment z w ∧
      c.length = dist z w ∧ IsOriginalGeodesicArc M p := by
  obtain ⟨a, b, γ, s, t, _ha, _hb, _hab, hγ, hline, hst, rfl, rfl, _⟩ :=
    exists_ordered_geodesic_distance_crossRatio z w hzw
  obtain ⟨c, p, hpc, hpoint, hlength, harc⟩ :=
    M.exists_projected_geodesic_arc_path ⟨hγ, hline⟩ s t hst hinj
  have htime : range (fun u : I => s + (t - s) * (u : ℝ)) = Icc s t := by
    calc
      _ = range (Subtype.val ∘ (iccHomeoI s t hst).symm) := by
        congr 1
        funext u
        simp only [Function.comp_apply, iccHomeoI_symm_apply_coe]
        ring
      _ = range (Subtype.val : Icc s t → ℝ) :=
        (iccHomeoI s t hst).symm.surjective.range_comp _
      _ = Icc s t := Subtype.range_val
  have htrace : range p = M.halfPlaneCover '' closedHSegment (γ s) (γ t) := by
    have hfun : (p : I → X) =
        M.halfPlaneCover ∘ γ ∘ (fun u : I => s + (t - s) * (u : ℝ)) := funext hpoint
    rw [hfun, range_comp, range_comp, htime,
      ← closedHSegment_eq_image_Icc ⟨hγ, hline⟩ hst]
  have hdist : dist (γ s) (γ t) = t - s := by
    rw [hγ.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst.le), neg_sub]
  exact ⟨c, p, hpc, htrace, hlength.trans hdist.symm, harc⟩

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Surfaces

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "D" => HalfPlaneFuchsianGroup.cayleyData P
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout
local notation "M" => threeBoundaryQuotientModel D
  (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)
local notation "π" =>
  orbitProjection (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) ℍ
local notation "Φ" => annularPairCayleyOrbitHomeomorph E r x hE hr hin hout

/-- Each original mirror's closed six-foot interval supplies an actual finite
geodesic C1 path on the unchanged original surface. The raw mirror order is
`(p12,p13), (p21,p23), (p32,p31)`. -/
theorem annularSixFeet_original_geodesic_c1_arcs
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    let u : Fin 3 → ℍ := ![p12, p21, p32]
    let v : Fin 3 → ℍ := ![p13, p23, p31]
    ∀ i : Fin 3, ∃ (c : HyperbolicSurfaceC1CurvePiece M)
      (p : Path ((M).halfPlaneCover (u i)) ((M).halfPlaneCover (v i))),
      (∀ t : I, p t = c.curve t) ∧
      range p = (M).halfPlaneCover '' closedHSegment (u i) (v i) ∧
      c.length = dist (u i) (v i) ∧ IsOriginalGeodesicArc M p := by
  obtain ⟨hinj0, hinj1, hinj2⟩ :=
    annularSixFeet_orbitProjection_injOn_closed_mirror_segments E r x hE hr hin hout hB
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  have hx : 0 < x := (add_pos zero_lt_one hr).trans hin
  obtain ⟨hne0, hne1, hne2⟩ :=
    annular_common_perpendicular_feet_ne E r x (zero_lt_one.trans hE) hr hE hx
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  have hcover (z : ℍ) : (M).halfPlaneCover z = Φ (π z) := by
    rw [annularPairCayleyOrbitHomeomorph_projection E r x hE hr hin hout]
    rfl
  have htransfer {A : Set ℍ} (hi : InjOn π A) : InjOn (M).halfPlaneCover A := by
    intro z hz w hw he
    apply hi hz hw
    apply (Φ).injective
    rw [← hcover z, ← hcover w]
    exact he
  dsimp only
  intro i
  fin_cases i
  · exact (M).exists_original_geodesic_c1_arc_between p12 p13 hne0 (htransfer hinj0)
  · exact (M).exists_original_geodesic_c1_arc_between p21 p23 hne1 (htransfer hinj1)
  · exact (M).exists_original_geodesic_c1_arc_between p32 p31 hne2.symm (htransfer hinj2)

end LowDimensionalTopology.Geometry.Hyperbolic
