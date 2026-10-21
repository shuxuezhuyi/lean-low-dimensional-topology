/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.TransversalLengths

/-!
# Actual distance-ratio loci and their necessary geometric correction
-/
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

def HalfPlaneLine.sinhDistanceRatioLocus (L M : HalfPlaneLine) (a b : ℝ) : Set ℍ :=
  {z | a*Real.sinh (L.pointDist z)=b*Real.sinh (M.pointDist z)}

def DiscLine.sinhDistanceRatioLocus (L M : DiscLine) (a b : ℝ) : Set 𝔻 :=
  {z | a*Real.sinh (L.pointDist z)=b*Real.sinh (M.pointDist z)}

theorem twice_abs_eq_abs_sub_one_iff (x : ℝ) :
    2*|x|=|x-1| ↔ x=(1 : ℝ)/3 ∨ x= -1 := by
  rw [←sq_eq_sq₀ (by positivity : 0≤2*|x|) (abs_nonneg (x-1)),mul_pow,sq_abs,sq_abs]
  constructor
  · intro h
    have he : (3*x-1)*(x+1)=0:=by nlinarith only [h]
    rcases mul_eq_zero.mp he with he|he
    · exact Or.inl (by linarith only [he])
    · exact Or.inr (by linarith only [he])
  · rintro (rfl|rfl) <;> norm_num

theorem vertical_distance_ratio_locus_two_lines :
    (HalfPlaneLine.vertical 0).sinhDistanceRatioLocus (.vertical 1) 2 1=
      (HalfPlaneLine.vertical ((1 : ℝ)/3)).carrier ∪ (HalfPlaneLine.vertical (-1)).carrier := by
  ext z
  change 2*Real.sinh ((HalfPlaneLine.vertical 0).pointDist z)=
    1*Real.sinh ((HalfPlaneLine.vertical 1).pointDist z) ↔ _
  rw [verticalLine_pointDist_sinh,verticalLine_pointDist_sinh,sub_zero,one_mul,
    ←mul_div_assoc,div_left_inj' z.im_ne_zero,twice_abs_eq_abs_sub_one_iff]
  rfl

theorem vertical_distance_ratio_locus_not_geodesic :
    ¬∃N : HalfPlaneLine,(HalfPlaneLine.vertical 0).sinhDistanceRatioLocus (.vertical 1) 2 1=N.carrier := by
  rintro ⟨N,hN⟩
  rw [vertical_distance_ratio_locus_two_lines] at hN
  have hsub : (HalfPlaneLine.vertical ((1 : ℝ)/3)).carrier⊆N.carrier := by
    rw [←hN]
    exact subset_union_left
  obtain ⟨p,q,hp,hq,hpq⟩:=(HalfPlaneLine.vertical ((1 : ℝ)/3)).exists_two_points
  have he := N.eq_of_two_points (.vertical ((1 : ℝ)/3)) hpq (hsub hp) (hsub hq) hp hq
  let z:=metricProbe (-1) 1 (by norm_num)
  have hz : z∈(HalfPlaneLine.vertical (-1)).carrier:=rfl
  have hzN : z∈N.carrier:=hN ▸ mem_union_right _ hz
  rw [he] at hzN
  change (-1 : ℝ)=(1 : ℝ)/3 at hzN
  norm_num at hzN

/-- Even either generating line is omitted by the source requirement that both coefficients
be strictly positive. This is independent of the additional whole-locus problem. -/
theorem vertical_generator_not_positive_ratio_locus (a b : ℝ) (hb : 0<b) :
    (HalfPlaneLine.vertical 0).carrier≠(HalfPlaneLine.vertical 0).sinhDistanceRatioLocus (.vertical 1) a b := by
  intro he
  have hI : UpperHalfPlane.I∈(HalfPlaneLine.vertical 0).carrier:=rfl
  have hh:=he ▸ hI
  change a*Real.sinh ((HalfPlaneLine.vertical 0).pointDist UpperHalfPlane.I)=
    b*Real.sinh ((HalfPlaneLine.vertical 1).pointDist UpperHalfPlane.I) at hh
  rw [verticalLine_pointDist_sinh,verticalLine_pointDist_sinh,UpperHalfPlane.I_re,UpperHalfPlane.I_im] at hh
  norm_num at hh
  exact hb.ne' hh.symm

theorem DiscLine.sinhDistanceRatioLocus_eq_cayley (L M : DiscLine) (a b : ℝ) :
    L.sinhDistanceRatioLocus M a b=
      halfPlaneToDisc '' L.toHalfPlane.sinhDistanceRatioLocus M.toHalfPlane a b := by
  ext z
  constructor
  · intro hz
    refine ⟨discToHalfPlane z,?_,halfPlaneToDisc_discToHalfPlane z⟩
    change a*Real.sinh (L.toHalfPlane.pointDist (discToHalfPlane z))=
      b*Real.sinh (M.toHalfPlane.pointDist (discToHalfPlane z))
    simpa only [HalfPlaneLine.sinhDistanceRatioLocus,DiscLine.sinhDistanceRatioLocus,
      mem_ofPred_eq,L.pointDist_eq_halfPlane,M.pointDist_eq_halfPlane] using hz
  · rintro ⟨w,hw,rfl⟩
    change a*Real.sinh (L.pointDist (halfPlaneToDisc w))=
      b*Real.sinh (M.pointDist (halfPlaneToDisc w))
    rw [L.pointDist_eq_halfPlane,M.pointDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc]
    exact hw

end
end LowDimensionalTopology.Geometry.Hyperbolic
