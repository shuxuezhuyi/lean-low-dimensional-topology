module
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleInradius
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.LineBisectors
@[expose] public section
open Set Matrix
open scoped UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

theorem HalfPlaneLine.closedCarrier_mem_ideal_iff (L : HalfPlaneLine) (p : ClosedHalfPlaneModel)
    (hp : p.val ∈ halfPlaneIdealBoundary) : p ∈ L.closedCarrier ↔ p.val ∈ L.idealEndpoints := by
  have he := L.toDiscLine.closedCarrier_ideal_iff_halfPlane (closedModelCayleyHomeomorph p)
    (closedModelCayley_ideal_norm p hp)
  rw [L.toDiscLine_toHalfPlane,closedModelCayley_toExtended,extendedCayley.symm_apply_apply] at he
  rw [← L.cayley_image_closedCarrier] at he
  exact (closedModelCayleyHomeomorph.injective.mem_set_image).symm.trans he.symm

def twoIdealAngleVertex (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) : ℍ :=
  ⟨⟨Real.cos α,Real.sin α⟩,Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2⟩

theorem twoIdealAngleVertex_norm (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    ‖(twoIdealAngleVertex α hα : ℂ)‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← Complex.normSq_eq_norm_sq]
  simp only [twoIdealAngleVertex,Complex.normSq_apply,one_pow]
  nlinarith only [Real.sin_sq_add_cos_sq α]

def twoIdealNegativeEndpoint : ClosedHalfPlaneModel :=
  ⟨(((-1 : ℂ) : OnePoint ℂ)),(coe_mem_closedHalfPlaneSet _).mpr (by norm_num)⟩

def twoIdealInfiniteEndpoint : ClosedHalfPlaneModel := ⟨∞,by simp [closedHalfPlaneSet]⟩

theorem twoIdealNegativeEndpoint_ideal : twoIdealNegativeEndpoint.val ∈ halfPlaneIdealBoundary := by
  exact (coe_mem_halfPlaneIdealBoundary (-1)).mpr (by norm_num)

theorem twoIdealInfiniteEndpoint_ideal : twoIdealInfiniteEndpoint.val ∈ halfPlaneIdealBoundary := by
  simp [twoIdealInfiniteEndpoint,halfPlaneIdealBoundary]

/-- A genuine H triangle with prescribed finite angle and two actual ideal vertices. -/
def twoIdealAngleHTriangle (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) : ClosedHTriangle where
  a := halfPlaneToClosedModel (twoIdealAngleVertex α hα)
  b := twoIdealNegativeEndpoint
  c := twoIdealInfiniteEndpoint
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    have hA := (L.closedCarrier_mem_interior_iff _).mp ha
    have hB := (L.closedCarrier_mem_ideal_iff _ twoIdealNegativeEndpoint_ideal).mp hb
    have hC := (L.closedCarrier_mem_ideal_iff _ twoIdealInfiniteEndpoint_ideal).mp hc
    obtain ⟨x,rfl⟩ := L.eq_vertical_of_infty_ideal hC
    have hAx : Real.cos α = x := hA
    rw [vertical_idealEndpoints] at hB
    change ((-1 : ℂ) : OnePoint ℂ) ∈ {((x : ℂ) : OnePoint ℂ),∞} at hB
    simp only [mem_insert_iff,mem_singleton_iff,OnePoint.coe_ne_infty,or_false] at hB
    have hreal := congrArg Complex.re (OnePoint.coe_injective hB)
    simp only [Complex.neg_re,Complex.one_re,Complex.ofReal_re] at hreal
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hα.1.le (le_refl Real.pi) hα.2
    rw [Real.cos_pi] at hcos
    linarith only [hAx,hreal,hcos]

def twoIdealAngleTriangle (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) : ClosedDiscTriangle :=
  (twoIdealAngleHTriangle α hα).toDiscTriangle


theorem twoIdealAngleTriangle_ideal (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    ‖((twoIdealAngleTriangle α hα).b : ℂ)‖ = 1 ∧ ‖((twoIdealAngleTriangle α hα).c : ℂ)‖ = 1 :=
  ⟨closedModelCayley_ideal_norm _ twoIdealNegativeEndpoint_ideal,
    closedModelCayley_ideal_norm _ twoIdealInfiniteEndpoint_ideal⟩

theorem twoIdealAngleTriangle_circular_side (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    (twoIdealAngleTriangle α hα).sideLineC.toHalfPlane = HalfPlaneLine.circle 0 1 (by norm_num) := by
  let T := twoIdealAngleTriangle α hα
  let z := twoIdealAngleVertex α hα
  have hz : halfPlaneToClosedModel z ∈ T.sideLineC.toHalfPlane.closedCarrier :=
    (T.sideLineC.closedCarrier_cayley_mem _).mp T.a_mem_sideLineC
  have hp : twoIdealNegativeEndpoint ∈ T.sideLineC.toHalfPlane.closedCarrier :=
    (T.sideLineC.closedCarrier_cayley_mem _).mp T.b_mem_sideLineC
  refine T.sideLineC.toHalfPlane.eq_of_shared_ideal_and_interior _ z
    ((T.sideLineC.toHalfPlane.closedCarrier_mem_interior_iff z).mp hz) ?_
    (((-1 : ℂ) : OnePoint ℂ)) ?_ ?_
  · change ‖(z : ℂ) - (0 : ℂ)‖ = 1
    rw [sub_zero]
    exact twoIdealAngleVertex_norm α hα
  · exact (T.sideLineC.toHalfPlane.closedCarrier_mem_ideal_iff _ twoIdealNegativeEndpoint_ideal).mp hp
  · rw [circle_idealEndpoints]
    norm_num

theorem twoIdealAngleTriangle_alpha (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    (twoIdealAngleTriangle α hα).alpha = α := by
  let T := twoIdealAngleTriangle α hα
  let z := twoIdealAngleVertex α hα
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hα.1.le (le_refl Real.pi) hα.2
  rw [Real.cos_pi] at hcos
  have hn : (z : ℂ).re ≠ (-1 : ℂ).re := by
    change Real.cos α ≠ -1
    linarith only [hcos]
  have hL : ((1 : GL (Fin 2) ℝ) • · : ℍ → ℍ) '' T.sideLineC.toHalfPlane.carrier =
      (HalfPlaneLine.circle 0 1 (by norm_num)).carrier := by
    rw [twoIdealAngleTriangle_circular_side α hα]
    simp only [one_smul,image_id']
  have hEnd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix (1 : GL (Fin 2) ℝ))
      (extendedCayley.symm (closedDiscToExtended T.c)) = ∞ := by
    change Mobius.fractionalLinear (complexifiedRealMobiusMatrix (1 : GL (Fin 2) ℝ))
      (extendedCayley.symm (closedDiscToExtended (closedModelCayleyHomeomorph twoIdealInfiniteEndpoint))) = ∞
    rw [closedModelCayley_toExtended,extendedCayley.symm_apply_apply]
    simp [complexifiedRealMobiusMatrix,Mobius.fractionalLinear_one,twoIdealInfiniteEndpoint]
  have hA : Mobius.fractionalLinear (complexifiedRealMobiusMatrix (1 : GL (Fin 2) ℝ))
      (extendedCayley.symm (closedDiscToExtended T.a)) = ((z : ℂ) : OnePoint ℂ) := by
    change Mobius.fractionalLinear (complexifiedRealMobiusMatrix (1 : GL (Fin 2) ℝ))
      (extendedCayley.symm (closedDiscToExtended (closedModelCayleyHomeomorph (halfPlaneToClosedModel z)))) = _
    rw [closedModelCayley_toExtended,extendedCayley.symm_apply_apply]
    simp [complexifiedRealMobiusMatrix,Mobius.fractionalLinear_one,halfPlaneToClosedModel]
  have hB : Mobius.fractionalLinear (complexifiedRealMobiusMatrix (1 : GL (Fin 2) ℝ))
      (extendedCayley.symm (closedDiscToExtended T.b)) = ((-1 : ℂ) : OnePoint ℂ) := by
    change Mobius.fractionalLinear (complexifiedRealMobiusMatrix (1 : GL (Fin 2) ℝ))
      (extendedCayley.symm (closedDiscToExtended (closedModelCayleyHomeomorph twoIdealNegativeEndpoint))) = _
    rw [closedModelCayley_toExtended,extendedCayley.symm_apply_apply]
    simp [complexifiedRealMobiusMatrix,Mobius.fractionalLinear_one,twoIdealNegativeEndpoint]
  have he := T.alpha_cos_normalized (twoIdealAngleTriangle_ideal α hα).2 1 (by norm_num)
    hL hEnd (z : ℂ) (-1) (twoIdealAngleVertex_norm α hα) (by norm_num) hn hA hB
  have hnot : ¬ (z : ℂ).re < (-1 : ℂ).re := by
    change ¬ Real.cos α < -1
    linarith only [hcos]
  rw [ite_eq_right hnot] at he
  change Real.cos T.alpha = Real.cos α at he
  exact Real.strictAntiOn_cos.injOn ⟨T.alpha_mem_Ico.1,T.alpha_mem_Ico.2.le⟩
    ⟨hα.1.le,hα.2.le⟩ he

/-- Prescribed source angles are realized by an actual finite-or-ideal native triangle. -/
theorem exists_two_ideal_triangle_with_angle (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    ∃ T : ClosedDiscTriangle, T.alpha = α ∧ ‖(T.b : ℂ)‖ = 1 ∧ ‖(T.c : ℂ)‖ = 1 :=
  ⟨twoIdealAngleTriangle α hα,twoIdealAngleTriangle_alpha α hα,twoIdealAngleTriangle_ideal α hα⟩


theorem real_mem_vertical_ideal_iff (a x : ℝ) :
    ((a : ℂ) : OnePoint ℂ) ∈ (HalfPlaneLine.vertical x).idealEndpoints ↔ a = x := by
  simp [vertical_idealEndpoints]

def allIdealZeroEndpoint : ClosedHalfPlaneModel :=
  ⟨((0 : ℂ) : OnePoint ℂ),(coe_mem_closedHalfPlaneSet _).mpr (by norm_num)⟩

theorem allIdealZeroEndpoint_ideal : allIdealZeroEndpoint.val ∈ halfPlaneIdealBoundary :=
  (coe_mem_halfPlaneIdealBoundary 0).mpr (by norm_num)

def allIdealHTriangle : ClosedHTriangle where
  a := allIdealZeroEndpoint
  b := twoIdealNegativeEndpoint
  c := twoIdealInfiniteEndpoint
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    have hA := (L.closedCarrier_mem_ideal_iff _ allIdealZeroEndpoint_ideal).mp ha
    have hB := (L.closedCarrier_mem_ideal_iff _ twoIdealNegativeEndpoint_ideal).mp hb
    have hC := (L.closedCarrier_mem_ideal_iff _ twoIdealInfiniteEndpoint_ideal).mp hc
    obtain ⟨x,rfl⟩ := L.eq_vertical_of_infty_ideal hC
    have hAx : (0 : ℝ) = x := (real_mem_vertical_ideal_iff 0 x).mp hA
    change ((-1 : ℂ) : OnePoint ℂ) ∈ (HalfPlaneLine.vertical x).idealEndpoints at hB
    have hBx : (-1 : ℝ) = x := (real_mem_vertical_ideal_iff (-1) x).mp
      (by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hB)
    linarith only [hAx,hBx]

def allIdealDiscTriangle : ClosedDiscTriangle := allIdealHTriangle.toDiscTriangle

theorem allIdealDiscTriangle_ideal :
    ‖(allIdealDiscTriangle.a : ℂ)‖ = 1 ∧ ‖(allIdealDiscTriangle.b : ℂ)‖ = 1 ∧
      ‖(allIdealDiscTriangle.c : ℂ)‖ = 1 :=
  ⟨closedModelCayley_ideal_norm _ allIdealZeroEndpoint_ideal,
    closedModelCayley_ideal_norm _ twoIdealNegativeEndpoint_ideal,
    closedModelCayley_ideal_norm _ twoIdealInfiniteEndpoint_ideal⟩

/-- The endpoint angle zero is realized by the genuine three-ideal-vertex triangle. -/
theorem exists_two_ideal_triangle_with_angle_nonneg (α : ℝ) (hα : α ∈ Ico (0 : ℝ) Real.pi) :
    ∃ T : ClosedDiscTriangle, T.alpha = α ∧ ‖(T.b : ℂ)‖ = 1 ∧ ‖(T.c : ℂ)‖ = 1 := by
  by_cases hzero : α = 0
  · refine ⟨allIdealDiscTriangle,?_,allIdealDiscTriangle_ideal.2⟩
    rw [allIdealDiscTriangle.alpha_of_ideal allIdealDiscTriangle_ideal.1,hzero]
  · exact exists_two_ideal_triangle_with_angle α ⟨lt_of_le_of_ne hα.1 (Ne.symm hzero),hα.2⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
