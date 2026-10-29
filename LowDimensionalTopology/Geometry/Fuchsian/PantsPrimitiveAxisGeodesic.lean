module

public import LowDimensionalTopology.Geometry.Fuchsian.PantsQuotientModel
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalHyperbolicDeckGeodesic
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalSimpleClosedGeodesic

/-!
# The same primitive physical axis and actual period on the original quotient

This direct bridge uses the original group's literal quotient fibers. It does
not identify a newly selected uniformization subgroup with the original group.
-/

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups Pointwise

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces

private theorem pantsAxis_integer_equivariance
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (f : ℝ → ℍ)
    (hperiod : ∀ t : ℝ, f (t + 1) = A • f t) (n : ℤ) (t : ℝ) :
    A ^ n • f t = f (t + (n : ℝ)) := by
  have hstep (s : ℝ) : A • f s = f (s + 1) := (hperiod s).symm
  have hinv (s : ℝ) : A⁻¹ • f s = f (s - 1) := by
    calc
      A⁻¹ • f s = A⁻¹ • f ((s - 1) + 1) := by rw [sub_add_cancel]
      _ = A⁻¹ • (A • f (s - 1)) := by rw [hperiod]
      _ = f (s - 1) := inv_smul_smul A _
  induction n using Int.induction_on generalizing t with
  | zero => simp
  | succ n ih =>
    rw [zpow_add, zpow_one, mul_smul, hstep, ih]
    congr 1
    push_cast
    ring
  | pred n ih =>
    rw [zpow_sub, zpow_one, mul_smul, hinv, ih]
    congr 1
    push_cast
    ring

/-- Actual stability and full-stabilizer generation of the physical axis
construct a simple original closed geodesic with this matrix's full period. -/
theorem exists_original_simple_closed_geodesic_of_physical_primitive_axis
    {H : Subgroup complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hno : ∀ g ∈ H, g ≠ 1 → ¬ MobiusElliptic g)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (hg : cayleyMobius * realSLMobius A * cayleyMobius⁻¹ ∈ H)
    (hstable : MobiusStableSet H
      (cayleyMobius.val '' (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hA ht).carrier)))
    (hgen : mobiusSetStabilizer H
      (cayleyMobius.val '' (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hA ht).carrier)) =
        Subgroup.zpowers (cayleyMobius * realSLMobius A * cayleyMobius⁻¹)) :
    ∃ q : OriginalClosedGeodesic (threeBoundaryQuotientModel P hno),
      LiZhongQC.Covers (threeBoundaryQuotientModel P hno).halfPlaneCover A q.toLoop ∧
      Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → MobiusDomainQuotient P.domain) ∧
      range q.curve = mobiusDomainProjection P.domain ''
        (P.finiteCoordinate.symm '' (halfPlaneToDisc '' (hHyperbolicAxis A hA ht).carrier)) := by
  let M := threeBoundaryQuotientModel P hno
  let E : ℍ → P.domain.carrier := P.finiteCoordinate.symm ∘ halfPlaneToDisc
  let g := cayleyMobius * realSLMobius A * cayleyMobius⁻¹
  let S := cayleyMobius.val '' (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hA ht).carrier)
  have hE (z : ℍ) : (E z).val = cayleyMobius.val (halfPlaneBoundaryPoint z) := by
    have he := discFiniteHomeomorph_symm_coe (halfPlaneToDisc z)
    change _ = cayleyMobius.val (((z : ℂ) : ExtendedComplex))
    rw [cayleyMobius_apply, extendedCayley_halfPlane]
    exact he
  have hEinj : Function.Injective E :=
    P.finiteCoordinate.symm.injective.comp cayleyHomeomorph.injective
  have hEact (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
      (E (B • z)).val = (cayleyMobius * realSLMobius B * cayleyMobius⁻¹).val (E z).val := by
    have hB : halfPlaneBoundaryPoint (B • z) =
        (realSLMobius B).val (halfPlaneBoundaryPoint z) := (realSLMobius_action B z).symm
    rw [hE, hE, hB]
    change cayleyMobius • (realSLMobius B • halfPlaneBoundaryPoint z) =
      (cayleyMobius * realSLMobius B * cayleyMobius⁻¹) •
        (cayleyMobius • halfPlaneBoundaryPoint z)
    simp only [mul_smul, inv_smul_smul]
  have hgpow (n : ℤ) : cayleyMobius * realSLMobius (A ^ n) * cayleyMobius⁻¹ = g ^ n := by
    change (MulAut.conj cayleyMobius) (realSLMobius (A ^ n)) =
      ((MulAut.conj cayleyMobius) (realSLMobius A)) ^ n
    rw [map_zpow, map_zpow]
  have hdeck (z : ℍ) : M.halfPlaneCover (A • z) = M.halfPlaneCover z := by
    change mobiusDomainProjection P.domain (E (A • z)) = mobiusDomainProjection P.domain (E z)
    apply Quotient.sound
    exact ⟨⟨g, hg⟩, Subtype.ext (hEact A z).symm⟩
  obtain ⟨γ, hγ, hγaxis, hT, hperiod⟩ := exists_unitSpeed_axis_with_actual_period A hA ht
  let T := hTranslationLength (hSLIsometry A)
  let f : ℝ → ℍ := fun t => γ (T * t)
  have hfperiod (t : ℝ) : f (t + 1) = A • f t := by
    change γ (T * (t + 1)) = A • γ (T * t)
    rw [mul_add, mul_one, hperiod]
  have hfinj : Function.Injective f := by
    intro s t hst
    exact mul_left_cancel₀ hT.ne' (hγ.1.injective hst)
  have hfull : range f = (hHyperbolicAxis A hA ht).carrier := by
    rw [← hγaxis]
    apply subset_antisymm
    · rintro _ ⟨t, rfl⟩
      exact ⟨T * t, rfl⟩
    · rintro _ ⟨s, rfl⟩
      refine ⟨s / T, ?_⟩
      change γ (T * (s / T)) = γ s
      exact congrArg γ (mul_div_cancel₀ s (show T ≠ 0 from hT.ne'))
  have hmem (t : ℝ) : (E (f t)).val ∈ S := by
    rw [hE]
    exact mem_image_of_mem _ ⟨f t, hfull ▸ mem_range_self t, rfl⟩
  let q : OriginalClosedGeodesic M :=
    { curve := M.halfPlaneCover ∘ f
      locallyMinimizing := by
        simpa only [zero_add, Function.comp_def, f] using
          M.original_locallyMinimizingArc_projected_affine_geodesic hγ 0 T hT
      periodic := by
        intro t
        change M.halfPlaneCover (f (t + 1)) = M.halfPlaneCover (f t)
        rw [hfperiod, hdeck] }
  have hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop := by
    refine ⟨f, (hγ.1.continuous.comp (continuous_const.mul continuous_id)).continuousOn, ?_, ?_⟩
    · intro t htI
      rw [Path.extend_apply q.toLoop.2 htI]
      rfl
    · simpa only [zero_add] using hfperiod 0
  refine ⟨q, hcov, ?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro s t hst
    change mobiusDomainProjection P.domain (E (f s)) = mobiusDomainProjection P.domain (E (f t)) at hst
    obtain ⟨k, hkt⟩ := Quotient.exact hst.symm
    have hmove : k.val.val (E (f s)).val = (E (f t)).val := congrArg Subtype.val hkt
    have hkstab := mobiusStableSet_mem_stabilizer_of_intersection hstable k.val k.property
      ⟨(E (f t)).val, ⟨(E (f s)).val, hmem s, hmove⟩, hmem t⟩
    rw [hgen] at hkstab
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hkstab
    have hact : E (A ^ n • f s) = E (f t) := by
      apply Subtype.ext
      rw [hEact, hgpow, hn]
      exact hmove
    have hts : t = s + (n : ℝ) := hfinj
      ((hEinj hact).symm.trans (pantsAxis_integer_equivariance A f hfperiod n s))
    have hnzero : ((n : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨n, by simp⟩
    change (s : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ))
    rw [hts, AddCircle.coe_add, hnzero, add_zero]
  · change range ((mobiusDomainProjection P.domain ∘ E) ∘ f) = _
    rw [range_comp, hfull]
    simp only [E, image_image, Function.comp_def]

end LowDimensionalTopology.Geometry.Fuchsian
