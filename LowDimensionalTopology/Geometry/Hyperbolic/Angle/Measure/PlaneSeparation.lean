module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.PlaneSeparation
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Hyperbolic
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc ENNReal Classical
noncomputable section


/-- Distinct disjoint actual open convex regions can overlap in only finitely many directions at a common basepoint. -/
theorem finite_discRadialDirections_common_closures {U V : Set Complex.UnitDisc}
    (hUc : DiscHConvex U) (hUo : IsOpen U) (hUn : U.Nonempty)
    (hVc : DiscHConvex V) (hVo : IsOpen V) (hVn : V.Nonempty)
    (hd : Disjoint U V) (h0U : (0 : Complex.UnitDisc) ∈ closure U)
    (h0V : (0 : Complex.UnitDisc) ∈ closure V) :
    (discRadialDirections (closure U) ∩ discRadialDirections (closure V)).Finite := by
  have hdis : Disjoint (kleinCoordinate '' U) (kleinCoordinate '' V) :=
    hd.image kleinCoordinate_injective.injOn (subset_univ _) (subset_univ _)
  obtain ⟨n, t, hn, hline⟩ := Auxiliary.Analysis.convex_open_disjoint_closures_hyperplane
    ((discHConvex_iff_klein_convex _).mp hUc) (isOpenEmbedding_kleinCoordinate.isOpenMap U hUo)
    (hUn.image kleinCoordinate) ((discHConvex_iff_klein_convex _).mp hVc)
    (isOpenEmbedding_kleinCoordinate.isOpenMap V hVo) (hVn.image kleinCoordinate) hdis
  have hUsub := image_closure_subset_closure_image continuous_kleinCoordinate (s := U)
  have hVsub := image_closure_subset_closure_image continuous_kleinCoordinate (s := V)
  have ht : t = 0 := by
    have hh := hline (kleinCoordinate 0)
      ⟨hUsub (mem_image_of_mem _ h0U), hVsub (mem_image_of_mem _ h0V)⟩
    simpa [kleinCoordinate, poincareToKlein, kleinFormula] using hh.symm
  rw [← discRadialDirections_inter hUc.closure hVc.closure h0U h0V]
  apply (finite_circle_orthogonal n hn).subset
  rintro u ⟨r, hr⟩
  have he := hline (kleinCoordinate (discRadialPoint r u))
    ⟨hUsub (mem_image_of_mem _ hr.1), hVsub (mem_image_of_mem _ hr.2)⟩
  rw [ht, kleinCoordinate_discRadialPoint, real_inner_comm] at he
  change inner ℝ ((2 * r.val / (1 + r.val ^ 2)) • (u : ℂ)) n = 0 at he
  rw [real_inner_smul_left, mul_eq_zero] at he
  exact he.resolve_left (ne_of_gt (div_pos (mul_pos (by norm_num) r.property.1) (by positivity)))


end
end LowDimensionalTopology.Geometry.Hyperbolic
