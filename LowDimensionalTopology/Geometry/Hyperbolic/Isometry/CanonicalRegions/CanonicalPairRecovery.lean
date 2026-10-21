/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalReconstruction
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.ParabolicHoroballs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A parabolic map is determined by its unique fixed point and one moved point with its image. -/
theorem mobius_parabolic_eq_of_fixed_points_and_one_value
    (f g : Mobius.complexMobiusGroup) (hf : Mobius.MobiusParabolic f) (p : Mobius.ExtendedComplex)
    (hp : f.val p ≠ p)
    (hfix : ∀ z : Mobius.ExtendedComplex, f.val z = z ↔ g.val z = z)
    (hvalue : f.val p = g.val p) : f = g := by
  obtain ⟨q,hq⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.parabolic_translation_conjugate f hf
  let G : Mobius.complexMobiusGroup := q⁻¹*g*q
  have hGfix (z : Mobius.ExtendedComplex) : G.val z=z ↔ z=∞ := by
    change q.val.symm (g.val (q.val z))=z ↔ z=∞
    rw [Equiv.symm_apply_eq]
    rw [← hfix]
    rw [hq]
    change q.val ((DiscreteGroups.mobiusTranslation 1).val (q.val.symm (q.val z)))=q.val z ↔ _
    rw [Equiv.symm_apply_apply,q.val.injective.eq_iff]
    cases z using OnePoint.rec with
    | infty => simp only [DiscreteGroups.mobiusTranslation_infty]
    | coe z => simp [DiscreteGroups.mobiusTranslation_coe]
  have hGi : G.val ∞=∞ := (hGfix ∞).mpr rfl
  have hGpar : Mobius.MobiusBoundaryParabolic G := by
    refine ⟨?_,∞,hGfix⟩
    intro he
    have h0 := (hGfix (0 : ℂ)).mp (by rw [he];rfl)
    exact OnePoint.coe_ne_infty (0 : ℂ) h0
  let G' : Mobius.mobiusInftyStabilizer := ⟨G,hGi⟩
  obtain ⟨b,hb⟩ := (DiscreteGroups.mobiusMultiplier_eq_one_iff_translation G').mp
    ((DiscreteGroups.mobiusMultiplier_eq_one_iff_parabolic_or_identity G').mpr (Or.inl hGpar))
  change G=DiscreteGroups.mobiusTranslation b at hb
  have hpinfty : q.val.symm p ≠ ∞ := by
    intro he
    apply hp
    rw [hq]
    change q.val ((DiscreteGroups.mobiusTranslation 1).val (q.val.symm p))=p
    rw [he,DiscreteGroups.mobiusTranslation_infty]
    exact (q.val.symm_apply_eq.mp he).symm
  obtain ⟨z,hz⟩ : ∃ z : ℂ, (z : Mobius.ExtendedComplex)=q.val.symm p := by
    generalize hh : q.val.symm p = u at *
    cases u using OnePoint.rec with
    | infty => exact (hpinfty rfl).elim
    | coe z => exact ⟨z,rfl⟩
  have he : (DiscreteGroups.mobiusTranslation 1).val (z : Mobius.ExtendedComplex) = (DiscreteGroups.mobiusTranslation
    b).val (z : Mobius.ExtendedComplex) := by
    have hv := congrArg q.val.symm hvalue
    have hGp : G.val (q.val.symm p)=q.val.symm (g.val p) := by
      change q.val.symm (g.val (q.val (q.val.symm p)))=q.val.symm (g.val p)
      rw [Equiv.apply_symm_apply]
    rw [← hGp,hq] at hv
    change q.val.symm (q.val ((DiscreteGroups.mobiusTranslation 1).val (q.val.symm p)))=G.val (q.val.symm p) at hv
    rw [Equiv.symm_apply_apply,← hz,hb] at hv
    exact hv
  rw [DiscreteGroups.mobiusTranslation_coe,DiscreteGroups.mobiusTranslation_coe,OnePoint.coe_eq_coe] at he
  have hb1 : b=1 := by linear_combination -he
  have hG : G=DiscreteGroups.mobiusTranslation 1 := by simpa only [hb1] using hb
  calc
    f=q*DiscreteGroups.mobiusTranslation 1*q⁻¹ := hq
    _=q*G*q⁻¹ := by rw [hG]
    _=g := by dsimp [G];group

/-- Two actual Mobius maps with the same fixed points and one moved value coincide. -/
theorem mobius_eq_of_fixed_points_and_one_value
    (f g : Mobius.complexMobiusGroup) (p : Mobius.ExtendedComplex) (hp : f.val p ≠ p)
    (hfix : ∀ z : Mobius.ExtendedComplex, f.val z = z ↔ g.val z = z)
    (hvalue : f.val p = g.val p) : f = g := by
  have hf : f≠1 := by intro he;apply hp;rw [he];rfl
  rcases Mobius.mobius_nonidentity_fixedPoint_dichotomy f hf with ⟨a,ha⟩ | ⟨a,b,hab,hfixed⟩
  · exact mobius_parabolic_eq_of_fixed_points_and_one_value f g ⟨hf,a,ha⟩ p hp hfix hvalue
  · have ha : f.val a=a := (hfixed a).mpr (Or.inl rfl)
    have hb : f.val b=b := (hfixed b).mpr (Or.inr rfl)
    have hpa : a≠p := by rintro rfl;exact hp ha
    have hpb : b≠p := by rintro rfl;exact hp hb
    exact Mobius.mobius_eq_of_agree_triple f g a b p ⟨hab,hpa,hpb⟩
      (ha.trans ((hfix a).mp ha).symm) (hb.trans ((hfix b).mp hb).symm) hvalue

/-- Reversing the single observed pair accounts exactly for the inverse ambiguity. -/
theorem mobius_inverse_pair_of_fixed_points_and_image_pair
    (f g : Mobius.complexMobiusGroup) (p : Mobius.ExtendedComplex) (hp : f.val p ≠ p)
    (hfix : ∀ z : Mobius.ExtendedComplex, f.val z = z ↔ g.val z = z)
    (hpair : g.val p=f.val p ∨ g.val (f.val p)=p) : g=f ∨ g=f⁻¹ := by
  rcases hpair with hforward | hreverse
  · exact Or.inl (mobius_eq_of_fixed_points_and_one_value f g p hp hfix hforward.symm).symm
  · have hfixinv (z : Mobius.ExtendedComplex) : f.val z=z ↔ (g⁻¹).val z=z := by
      exact (hfix z).trans ⟨fun h=>Mobius.mobius_inv_fixed h,fun h=>by
        simpa only [inv_inv] using (Mobius.mobius_inv_fixed h)⟩
    have hvalue : f.val p=(g⁻¹).val p := by
      exact g.val.symm_apply_eq.mpr hreverse.symm |>.symm
    have he := mobius_eq_of_fixed_points_and_one_value f g⁻¹ p hp hfixinv hvalue
    right
    exact inv_injective (by simpa only [inv_inv] using he.symm)

/-- The same observed unordered pair permits only the original map or its inverse. -/
theorem mobius_inverse_pair_of_fixed_points_and_unordered_pair
    (f g : Mobius.complexMobiusGroup) (p q : Mobius.ExtendedComplex) (hp : f.val p ≠ p)
    (hfix : ∀ z : Mobius.ExtendedComplex, f.val z = z ↔ g.val z = z)
    (hpair : ({p,f.val p} : Set Mobius.ExtendedComplex)={q,g.val q}) : g=f ∨ g=f⁻¹ := by
  apply mobius_inverse_pair_of_fixed_points_and_image_pair f g p hp hfix
  rcases Set.pair_eq_pair_iff.mp hpair with ⟨hpq,himg⟩ | ⟨hpgq,hfpq⟩
  · left
    simpa only [← hpq] using himg.symm
  · right
    rw [hfpq]
    exact hpgq.symm

/-- The fixed points and one unoriented boundary-image pair determine the actual canonical region. -/
theorem hCanonicalRegion_eq_of_fixed_points_and_unordered_pair
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p q : Mobius.ExtendedComplex)
    (hp : (realSLMobius A).val p ≠ p)
    (hfix : ∀ z : Mobius.ExtendedComplex, (realSLMobius A).val z=z ↔ (realSLMobius B).val z=z)
    (hpair : ({p,(realSLMobius A).val p} : Set Mobius.ExtendedComplex)={q,(realSLMobius B).val q}) :
    hCanonicalRegion A=hCanonicalRegion B := by
  have hA : realSLMobius A≠1 := by intro he;apply hp;rw [he];rfl
  apply (hCanonicalRegion_eq_iff_inverse_pair A B hA).mpr
  rcases mobius_inverse_pair_of_fixed_points_and_unordered_pair
    (realSLMobius A) (realSLMobius B) p q hp hfix hpair with he | he
  · exact Or.inl he
  · exact Or.inr he

end LowDimensionalTopology.Geometry.Hyperbolic
