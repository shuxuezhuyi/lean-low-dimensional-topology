/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Ford.ComplexFordRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordOrdinaryOrbits
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal finite-coordinate part of an original sphere orbit. -/
def finiteMobiusOrbit (H : Subgroup complexMobiusGroup) (ξ : ExtendedComplex) : Set ℂ :=
  {z | (z:ExtendedComplex)∈MulAction.orbit H ξ}

/-- A true separating neighborhood at infinity bounds every actual finite orbit, for arbitrary complex Mobius groups. -/
theorem finiteMobiusOrbit_bounded (H : Subgroup complexMobiusGroup)
    (hsep : Fuchsian.HasSeparatingMobiusNeighborhood H ∞) (ξ : ExtendedComplex) :
    Bornology.IsBounded (finiteMobiusOrbit H ξ) := by
  obtain ⟨U,hU,hinf,hsepU⟩:=hsep
  obtain ⟨K,⟨_hKclosed,hKcompact⟩,hKU⟩:=OnePoint.hasBasis_nhds_infty.mem_iff.mp (hU.mem_nhds hinf)
  let O:=finiteMobiusOrbit H ξ
  let S:=O∩{w : ℂ | (w:ExtendedComplex)∈U}
  have hS : S.Subsingleton := by
    intro x hx y hy
    apply OnePoint.coe_injective
    exact Fuchsian.separating_orbit_inter_subsingleton H U hsepU ξ ⟨hx.1,hx.2⟩ ⟨hy.1,hy.2⟩
  apply (hKcompact.isBounded.union hS.finite.isBounded).subset
  intro w hw
  by_cases hwK : w∈K
  · exact Or.inl hwK
  · exact Or.inr ⟨hw,hKU (Or.inl ⟨w,hwK,rfl⟩)⟩

/-- Away from the actual orbit of infinity, a point of the original open discontinuity domain has a positive Euclidean gap from every original pole. -/
theorem finiteMobiusOrbit_infty_gap (H : Subgroup complexMobiusGroup)
    (D : Set ExtendedComplex) (ho : IsOpen D)
    (hinv : ∀g : H,∀x∈D,g • x∈D) (hd : DiscreteGroups.IsMobiusDiscontinuousOn H D)
    (hinf : (∞:ExtendedComplex)∈D) (z : ℂ) (hz : (z:ExtendedComplex)∈D)
    (hnot : (z:ExtendedComplex)∉MulAction.orbit H (∞:ExtendedComplex)) :
    ∃r : ℝ,0<r ∧ ∀p∈finiteMobiusOrbit H ∞,r≤‖z-p‖ := by
  let : MulAction H D:=DiscreteGroups.Action.invariantSubsetMulAction D hinv
  let : LocallyCompactSpace D:=ho.locallyCompactSpace
  let ξ : D:=⟨∞,hinf⟩
  have hdis : DiscreteGroups.Action.IsDiscontinuous H D := (DiscreteGroups.isMobiusDiscontinuousOn_iff_subtype H D
    hinv).mp hd
  have hclosed : IsClosed (MulAction.orbit H ξ):=hdis.isClosed_subset_orbit ξ (Subset.refl _)
  let U : Set ExtendedComplex:=Subtype.val '' (MulAction.orbit H ξ)ᶜ
  have hU : IsOpen U:=ho.isOpenMap_subtype_val _ hclosed.isOpen_compl
  have hzU : (z:ExtendedComplex)∈U := by
    refine ⟨⟨z,hz⟩,?_,rfl⟩
    rintro ⟨g,hg⟩
    exact hnot ⟨g,congrArg Subtype.val hg⟩
  have hV : IsOpen (((↑):ℂ→ExtendedComplex)⁻¹' U):=
    hU.preimage OnePoint.continuous_coe
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp hV z hzU
  refine ⟨r,hr,?_⟩
  intro p hp
  by_contra hle
  have hdist : dist p z<r := by simpa only [dist_eq_norm,norm_sub_rev p z] using not_le.mp hle
  obtain ⟨v,hv,hvp⟩:=hball hdist
  obtain ⟨g,hg⟩:=hp
  apply hv
  refine ⟨g,?_⟩
  apply Subtype.ext
  exact hg.trans hvp.symm


/-- A point outside the actual orbit of infinity is not a pole of any original group element. -/
theorem complexFord_den_ne_zero (H : Subgroup complexMobiusGroup) (z : ℂ)
    (hnot : (z:ExtendedComplex)∉MulAction.orbit H (∞:ExtendedComplex))
    (A : Auxiliary.Algebra.SpecialLinear2) (hA : mobiusSpecialLinearProjection A∈H) :
    A 1 0*z+A 1 1≠0 := by
  intro he
  have hmap : (mobiusSpecialLinearProjection A).val (z:ExtendedComplex)=∞ := by
    rw [specialLinear_projection_coe,fractionalLinear_coe]
    change (if A 1 0*z+A 1 1=0 then ∞ else (((A 0 0*z+A 0 1)/(A 1 0*z+A 1 1):ℂ):ExtendedComplex))=∞
    rw [ite_eq_left he]
  apply hnot
  refine ⟨⟨(mobiusSpecialLinearProjection A)⁻¹,H.inv_mem hA⟩,?_⟩
  change (mobiusSpecialLinearProjection A).val.symm ∞=(z:ExtendedComplex)
  rw [←hmap]
  exact Equiv.symm_apply_apply _ _

/-- The finite image of infinity under a genuine non-affine lift is an actual original orbit point. -/
theorem complexFord_infty_image_mem (H : Subgroup complexMobiusGroup)
    (A : Auxiliary.Algebra.SpecialLinear2) (hA : mobiusSpecialLinearProjection A∈H) (hc : A 1 0≠0) :
    A 0 0/A 1 0∈finiteMobiusOrbit H ∞ := by
  refine ⟨⟨mobiusSpecialLinearProjection A,hA⟩,?_⟩
  change (mobiusSpecialLinearProjection A).val ∞=((A 0 0/A 1 0:ℂ):ExtendedComplex)
  rw [specialLinear_projection_coe,fractionalLinear_infty]
  change (if A 1 0=0 then ∞ else ((A 0 0/A 1 0:ℂ):ExtendedComplex))=((A 0 0/A 1 0:ℂ):ExtendedComplex)
  rw [ite_eq_right hc]

/-- Every actual pole is the original inverse image of infinity. -/
theorem complexFord_pole_mem (H : Subgroup complexMobiusGroup)
    (A : Auxiliary.Algebra.SpecialLinear2) (hA : mobiusSpecialLinearProjection A∈H) (hc : A 1 0≠0) :
    -A 1 1/A 1 0∈finiteMobiusOrbit H ∞ := by
  have hmem := complexFord_infty_image_mem H A⁻¹ (by rw [map_inv];exact H.inv_mem hA)
    (by simpa only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.of_apply,
      Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.cons_val_fin_one,neg_ne_zero] using hc)
  simpa only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,div_neg,neg_div] using hmem

/-- The determinant-one norm is bounded by the sum of its four actual coefficient norms. -/
theorem matrixNorm_le_entry_sum (A : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.matrixNorm A≤‖A 0 0‖+‖A 0 1‖+‖A 1 0‖+‖A 1 1‖ := by
  have hsq : Auxiliary.Algebra.matrixNorm A^2≤(‖A 0 0‖+‖A 0 1‖+‖A 1 0‖+‖A 1 1‖)^2 := by
    rw [Auxiliary.Algebra.matrixNorm_sq]
    nlinarith [mul_nonneg (norm_nonneg (A 0 0)) (norm_nonneg (A 0 1)),
      mul_nonneg (norm_nonneg (A 0 0)) (norm_nonneg (A 1 0)),
      mul_nonneg (norm_nonneg (A 0 0)) (norm_nonneg (A 1 1)),
      mul_nonneg (norm_nonneg (A 0 1)) (norm_nonneg (A 1 0)),
      mul_nonneg (norm_nonneg (A 0 1)) (norm_nonneg (A 1 1)),
      mul_nonneg (norm_nonneg (A 1 0)) (norm_nonneg (A 1 1))]
  exact (sq_le_sq₀ (Auxiliary.Algebra.matrixNorm_nonneg _) (by positivity)).mp hsq

/-- A genuine original non-expanding denominator, bounded image and actual pole gap bound all four matrix coefficients. -/
theorem complexFord_coeff_norm_bound (A : Auxiliary.Algebra.SpecialLinear2) (hc : A 1 0≠0)
    (z : ℂ) (M B r : ℝ) (hM : 0≤M) (hB : 0≤B) (hr : 0<r)
    (hinfty : ‖A 0 0/A 1 0‖≤M) (hpole : ‖-A 1 1/A 1 0‖≤M)
    (hgap : r≤‖z-(-A 1 1/A 1 0)‖)
    (himage : ‖(A 0 0*z+A 0 1)/(A 1 0*z+A 1 1)‖≤B)
    (hden : ‖A 1 0*z+A 1 1‖≤1) :
    Auxiliary.Algebra.matrixNorm A≤2*M/r+1/r+B+(M/r)*‖z‖ := by
  have hcpos : 0<‖A 1 0‖:=norm_pos_iff.mpr hc
  have hfactor : A 1 0*z+A 1 1=A 1 0*(z-(-A 1 1/A 1 0)) := by field_simp;ring
  have hcR : ‖A 1 0‖≤1/r := by
    apply (le_div_iff₀ hr).mpr
    rw [hfactor,norm_mul] at hden
    nlinarith [mul_le_mul_of_nonneg_left hgap hcpos.le]
  have haR : ‖A 0 0‖≤M/r := by
    rw [norm_div] at hinfty
    have hh:=(div_le_iff₀ hcpos).mp hinfty
    have hh':=mul_le_mul_of_nonneg_left hcR hM
    simpa only [mul_one_div] using hh.trans hh'
  have hdR : ‖A 1 1‖≤M/r := by
    rw [norm_div,norm_neg] at hpole
    have hh:=(div_le_iff₀ hcpos).mp hpole
    have hh':=mul_le_mul_of_nonneg_left hcR hM
    simpa only [mul_one_div] using hh.trans hh'
  have hden0 : A 1 0*z+A 1 1≠0 := by
    rw [hfactor]
    exact mul_ne_zero hc (sub_ne_zero.mpr (by intro he;rw [he,sub_self,norm_zero] at hgap;linarith))
  have hnum : ‖A 0 0*z+A 0 1‖≤B := by
    rw [norm_div] at himage
    have hh:=(div_le_iff₀ (norm_pos_iff.mpr hden0)).mp himage
    exact hh.trans ((mul_le_mul_of_nonneg_left hden hB).trans_eq (mul_one B))
  have hbR : ‖A 0 1‖≤B+(M/r)*‖z‖ := by
    have ht:=norm_sub_le (A 0 0*z+A 0 1) (A 0 0*z)
    rw [add_sub_cancel_left,norm_mul] at ht
    exact ht.trans (add_le_add hnum (mul_le_mul_of_nonneg_right haR (norm_nonneg z)))
  have hn:=matrixNorm_le_entry_sum A
  rw [mul_div_assoc]
  linarith


/-- For an arbitrary original discontinuity domain, only finitely many determinant-one group lifts have non-expanding denominator at a point away from the infinity orbit. -/
theorem complexFord_subunit_lifts_finite (H : Subgroup complexMobiusGroup)
    (D : Set ExtendedComplex) (ho : IsOpen D)
    (hinv : ∀g : H,∀x∈D,g • x∈D) (hd : DiscreteGroups.IsMobiusDiscontinuousOn H D)
    (hinf : (∞:ExtendedComplex)∈D) (hfree : ∀g : H,g • (∞:ExtendedComplex)=∞→g=1)
    (z : ℂ) (hz : (z:ExtendedComplex)∈D)
    (hnot : (z:ExtendedComplex)∉MulAction.orbit H (∞:ExtendedComplex)) :
    {A : H.comap mobiusSpecialLinearProjection | ‖A.val 1 0*z+A.val 1 1‖≤1}.Finite := by
  have hsep:=Fuchsian.separatingMobiusNeighborhood_of_discontinuous H D ho hinv hd ∞ hinf hfree
  obtain ⟨M,hMpos,hM⟩:=(finiteMobiusOrbit_bounded H hsep ∞).exists_pos_norm_le
  obtain ⟨B,hBpos,hB⟩:=(finiteMobiusOrbit_bounded H hsep z).exists_pos_norm_le
  obtain ⟨r,hr,hgap⟩:=finiteMobiusOrbit_infty_gap H D ho hinv hd hinf z hz hnot
  let K:=H.comap mobiusSpecialLinearProjection
  let : DiscreteTopology K:=discreteMobius_preimage H
    (DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete H D hinv ⟨∞,hinf⟩ hd)
  let R:=max (2*M/r+1/r+B+(M/r)*‖z‖) (mobiusNormalizedNorm 1)
  apply (DiscreteGroups.MatrixGroups.finite_norm_bounded K R).subset
  intro A hden
  by_cases hc : A.val 1 0=0
  · have hfix : (mobiusSpecialLinearProjection A.val).val ∞=∞ := by
      rw [specialLinear_projection_coe]
      exact (Mobius.Classification.specialLinear_fixes_infty_iff A.val).mpr hc
    have he : mobiusSpecialLinearProjection A.val=1 :=
      congrArg Subtype.val (hfree ⟨mobiusSpecialLinearProjection A.val,A.property⟩ hfix)
    change Auxiliary.Algebra.matrixNorm A.val≤R
    rw [←mobiusNormalizedNorm_specialLinearProjection,he]
    exact le_max_right _ _
  · have hden0:=complexFord_den_ne_zero H z hnot A.val A.property
    have him : (A.val 0 0*z+A.val 0 1)/(A.val 1 0*z+A.val 1 1)∈finiteMobiusOrbit H z := by
      refine ⟨⟨mobiusSpecialLinearProjection A.val,A.property⟩,?_⟩
      change (mobiusSpecialLinearProjection A.val).val (z:ExtendedComplex)=_
      rw [specialLinear_projection_coe,fractionalLinear_coe]
      change (if A.val 1 0*z+A.val 1 1=0 then ∞ else
        (((A.val 0 0*z+A.val 0 1)/(A.val 1 0*z+A.val 1 1):ℂ):ExtendedComplex))=_
      rw [ite_eq_right hden0]
    have hi:=complexFord_infty_image_mem H A.val A.property hc
    have hp:=complexFord_pole_mem H A.val A.property hc
    exact (complexFord_coeff_norm_bound A.val hc z M B r hMpos.le hBpos.le hr
      (hM _ hi) (hM _ hp) (hgap _ hp) (hB _ him) hden).trans (le_max_left _ _)


/-- Denominators satisfy their actual multiplicative cocycle at every finite point avoiding the second map's pole. -/
theorem complexFord_den_mul (A B : Auxiliary.Algebra.SpecialLinear2) (z : ℂ)
    (hB : B 1 0*z+B 1 1≠0) :
    (A*B) 1 0*z+(A*B) 1 1=
      (A 1 0*((B 0 0*z+B 0 1)/(B 1 0*z+B 1 1))+A 1 1)*(B 1 0*z+B 1 1) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  field_simp [hB]
  ring

/-- The genuine closed common isometric-circle exterior, with the same non-affine convention as the source's open region. -/
def closedComplexFordRegion (H : Subgroup complexMobiusGroup) : Set ℂ :=
  {z | ∀A : Auxiliary.Algebra.SpecialLinear2,mobiusSpecialLinearProjection A∈H→A 1 0≠0→1≤‖A 1 0*z+A 1 1‖}

/-- The original group has an actual closed-Ford representative for every finite ordinary-domain orbit away from the infinity orbit. -/
theorem exists_closedComplexFord_representative (H : Subgroup complexMobiusGroup)
    (D : Set ExtendedComplex) (ho : IsOpen D)
    (hinv : ∀g : H,∀x∈D,g • x∈D) (hd : DiscreteGroups.IsMobiusDiscontinuousOn H D)
    (hinf : (∞:ExtendedComplex)∈D) (hfree : ∀g : H,g • (∞:ExtendedComplex)=∞→g=1)
    (z : ℂ) (hz : (z:ExtendedComplex)∈D)
    (hnot : (z:ExtendedComplex)∉MulAction.orbit H (∞:ExtendedComplex)) :
    ∃(B : Auxiliary.Algebra.SpecialLinear2) (w : ℂ),mobiusSpecialLinearProjection B∈H ∧
      (mobiusSpecialLinearProjection B).val (z:ExtendedComplex)=(w:ExtendedComplex) ∧
        (w:ExtendedComplex)∈D ∧ w∈closedComplexFordRegion H := by
  classical
  let K:=H.comap mobiusSpecialLinearProjection
  let F : Set K:={A | ‖A.val 1 0*z+A.val 1 1‖≤1}
  have hF : F.Finite:=complexFord_subunit_lifts_finite H D ho hinv hd hinf hfree z hz hnot
  have hne : F.Nonempty:=⟨1,by
    change ‖(1:Auxiliary.Algebra.SpecialLinear2) 1 0*z+(1:Auxiliary.Algebra.SpecialLinear2) 1 1‖≤1;norm_num⟩
  obtain ⟨B,hB,hmin⟩:=Set.exists_min_image F (fun A=>‖A.val 1 0*z+A.val 1 1‖) hF hne
  have hden0:=complexFord_den_ne_zero H z hnot B.val B.property
  let w:ℂ:=(B.val 0 0*z+B.val 0 1)/(B.val 1 0*z+B.val 1 1)
  have hBw : (mobiusSpecialLinearProjection B.val).val (z:ExtendedComplex)=(w:ExtendedComplex) := by
    rw [specialLinear_projection_coe,fractionalLinear_coe]
    change (if B.val 1 0*z+B.val 1 1=0 then ∞ else (w:ExtendedComplex))=(w:ExtendedComplex)
    rw [ite_eq_right hden0]
  refine ⟨B.val,w,B.property,hBw,?_,?_⟩
  · rw [←hBw]
    exact hinv ⟨mobiusSpecialLinearProjection B.val,B.property⟩ z hz
  · intro A hA _hc
    by_contra hle
    have hlt : ‖A 1 0*w+A 1 1‖<1:=not_le.mp hle
    let C : K:=⟨A,hA⟩*B
    have hcoc : ‖C.val 1 0*z+C.val 1 1‖=
        ‖A 1 0*w+A 1 1‖*‖B.val 1 0*z+B.val 1 1‖ := by
      rw [show C.val=A*B.val from rfl,complexFord_den_mul A B.val z hden0,norm_mul]
    have hsmall : ‖C.val 1 0*z+C.val 1 1‖<‖B.val 1 0*z+B.val 1 1‖ := by
      rw [hcoc]
      exact (mul_lt_mul_of_pos_right hlt (norm_pos_iff.mpr hden0)).trans_eq (one_mul _)
    have hCF : C∈F:=hsmall.le.trans hB
    exact (not_lt_of_ge (hmin C hCF)) hsmall


/-- The exact inverse-denominator norm identity includes the true matrix product. -/
theorem complexFord_den_inverse (B : Auxiliary.Algebra.SpecialLinear2) (z : ℂ) (hB : B 1 0*z+B 1 1≠0) :
    ‖B⁻¹ 1 0*((B 0 0*z+B 0 1)/(B 1 0*z+B 1 1))+B⁻¹ 1 1‖*
      ‖B 1 0*z+B 1 1‖=1 := by
  have hh:=congrArg norm (complexFord_den_mul B⁻¹ B z hB)
  rw [inv_mul_cancel] at hh
  have hleft : ‖(1:Auxiliary.Algebra.SpecialLinear2) 1 0*z+(1:Auxiliary.Algebra.SpecialLinear2) 1 1‖=1 := by norm_num
  rw [hleft,norm_mul] at hh
  exact hh.symm

/-- A strict genuine Ford point and a closed genuine Ford point in the same original orbit coincide. -/
theorem complexFord_strict_closed_orbit_unique (H : Subgroup complexMobiusGroup)
    (hfree : ∀g : H,g • (∞:ExtendedComplex)=∞→g=1)
    (z y : ℂ) (hz : z∈complexFordRegion H) (hy : y∈closedComplexFordRegion H)
    (g : H) (hgy : g.val.val (z:ExtendedComplex)=(y:ExtendedComplex)) : z=y := by
  by_cases hg : g=1
  · subst g
    exact OnePoint.coe_injective hgy
  obtain ⟨A,hA,hc⟩:=free_infty_nonidentity_has_isometricCircle H hfree g hg
  have hAden : 1<‖A 1 0*z+A 1 1‖:=hz A (hA ▸ g.property) hc
  have hden0 : A 1 0*z+A 1 1≠0:=norm_pos_iff.mp (zero_lt_one.trans hAden)
  have hval : (A 0 0*z+A 0 1)/(A 1 0*z+A 1 1)=y := by
    apply OnePoint.coe_injective
    rw [←hgy,←hA,specialLinear_projection_coe,fractionalLinear_coe]
    change (((A 0 0*z+A 0 1)/(A 1 0*z+A 1 1):ℂ):ExtendedComplex)=
      (if A 1 0*z+A 1 1=0 then ∞ else (((A 0 0*z+A 0 1)/(A 1 0*z+A 1 1):ℂ):ExtendedComplex))
    rw [ite_eq_right hden0]
  have hcInv : A⁻¹ 1 0≠0:=by
    simpa only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.of_apply,
      Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.cons_val_fin_one,neg_ne_zero] using hc
  have hyden:=hy A⁻¹ (by rw [map_inv,hA];exact H.inv_mem g.property) hcInv
  have hinv:=complexFord_den_inverse A z hden0
  rw [hval] at hinv
  have hmul:=mul_lt_mul_of_pos_left hAden
    (zero_lt_one.trans_le hyden)
  rw [mul_one,hinv] at hmul
  exact False.elim (not_lt_of_ge hyden hmul)

/-- The spherical closed common exterior includes the ordinary distinguished infinity point. -/
def extendedClosedComplexFordRegion (H : Subgroup complexMobiusGroup) : Set ExtendedComplex :=
  ((↑):ℂ→ExtendedComplex) '' closedComplexFordRegion H∪{∞}

/-- The genuine closed Ford region meets every original orbit of the full discontinuity domain. -/
theorem extendedClosedComplexFordRegion_meets_every_orbit (H : Subgroup complexMobiusGroup)
    (D : Set ExtendedComplex) (ho : IsOpen D)
    (hinv : ∀g : H,∀x∈D,g • x∈D) (hd : DiscreteGroups.IsMobiusDiscontinuousOn H D)
    (hinf : (∞:ExtendedComplex)∈D) (hfree : ∀g : H,g • (∞:ExtendedComplex)=∞→g=1)
    (ξ : ExtendedComplex) (hξ : ξ∈D) :
    ∃g : H,g • ξ∈D∩extendedClosedComplexFordRegion H := by
  by_cases horb : ξ∈MulAction.orbit H (∞:ExtendedComplex)
  · obtain ⟨g,hg⟩:=horb
    refine ⟨g⁻¹,?_⟩
    rw [←hg,inv_smul_smul]
    exact ⟨hinf,Or.inr rfl⟩
  · induction ξ using OnePoint.rec with
    | infty => exact False.elim (horb (MulAction.mem_orbit_self _))
    | coe z =>
      obtain ⟨B,w,hB,hBw,hwD,hw⟩:=exists_closedComplexFord_representative H D ho hinv hd hinf hfree z hξ horb
      refine ⟨⟨mobiusSpecialLinearProjection B,hB⟩,?_⟩
      change (mobiusSpecialLinearProjection B).val (z:ExtendedComplex)∈_
      rw [hBw]
      exact ⟨hwD,Or.inl ⟨w,hw,rfl⟩⟩


/-- The literal finite-coordinate membership of the spherical closed Ford region. -/
theorem extendedClosedComplexFordRegion_coe (H : Subgroup complexMobiusGroup) (z : ℂ) :
    (z:ExtendedComplex)∈extendedClosedComplexFordRegion H ↔ z∈closedComplexFordRegion H := by
  simp only [extendedClosedComplexFordRegion,mem_union,mem_image,OnePoint.coe_injective.eq_iff,
    exists_eq_right,mem_singleton_iff,OnePoint.coe_ne_infty,or_false]

/-- Strict common exterior points lie in the genuine closed common exterior. -/
theorem complexFordRegion_subset_closed (H : Subgroup complexMobiusGroup) :
    complexFordRegion H⊆closedComplexFordRegion H := by
  intro z hz A hA hc
  exact (hz A hA hc).le

/-- No finite closed-Ford point belongs to the distinguished infinity orbit. -/
theorem closedComplexFord_not_orbit_infty (H : Subgroup complexMobiusGroup)
    (hfree : ∀g : H,g • (∞:ExtendedComplex)=∞→g=1) (y : ℂ)
    (hy : y∈closedComplexFordRegion H) : (y:ExtendedComplex)∉MulAction.orbit H (∞:ExtendedComplex) := by
  rintro ⟨g,hg⟩
  have hgn : g≠1 := by
    intro he
    rw [he] at hg
    change (1:H) • (∞:ExtendedComplex)=(y:ExtendedComplex) at hg
    rw [one_smul] at hg
    exact OnePoint.infty_ne_coe y hg
  obtain ⟨A,hA,hc⟩:=free_infty_nonidentity_has_isometricCircle H hfree g hgn
  have hval : A 0 0/A 1 0=y := by
    apply OnePoint.coe_injective
    have hh : (mobiusSpecialLinearProjection A).val ∞=((A 0 0/A 1 0:ℂ):ExtendedComplex) := by
      rw [specialLinear_projection_coe,fractionalLinear_infty]
      change (if A 1 0=0 then ∞ else ((A 0 0/A 1 0:ℂ):ExtendedComplex))=_
      rw [ite_eq_right hc]
    rw [←hh,hA]
    exact hg
  have hcInv : A⁻¹ 1 0≠0:=by
    simpa only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.of_apply,
      Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.cons_val_fin_one,neg_ne_zero] using hc
  have hden : A⁻¹ 1 0*y+A⁻¹ 1 1=0 := by
    rw [←hval]
    simp only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.of_apply,
      Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.cons_val_fin_one]
    field_simp
    ring
  have hn:=hy A⁻¹ (by rw [map_inv,hA];exact H.inv_mem g.property) hcInv
  rw [hden,norm_zero] at hn
  norm_num at hn

/-- Spherical strict original Ford points are unique even among closed original Ford representatives. -/
theorem extendedComplexFord_strict_closed_orbit_unique (H : Subgroup complexMobiusGroup)
    (hfree : ∀g : H,g • (∞:ExtendedComplex)=∞→g=1)
    (x y : ExtendedComplex) (hx : x∈extendedComplexFordRegion H)
    (hy : y∈extendedClosedComplexFordRegion H) (g : H) (hgy : g • x=y) : x=y := by
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => rfl
    | coe y =>
      exact False.elim (closedComplexFord_not_orbit_infty H hfree y
        ((extendedClosedComplexFordRegion_coe H y).mp hy) ⟨g,hgy⟩)
  | coe x =>
    have hxF : x∈complexFordRegion H:=(extendedComplexFordRegion_coe H x).mp hx
    induction y using OnePoint.rec with
    | infty =>
      apply False.elim
      apply closedComplexFord_not_orbit_infty H hfree x (complexFordRegion_subset_closed H hxF)
      refine ⟨g⁻¹,?_⟩
      change g⁻¹ • (∞:ExtendedComplex)=(x:ExtendedComplex)
      rw [←hgy,inv_smul_smul]
    | coe y =>
      exact congrArg OnePoint.some (complexFord_strict_closed_orbit_unique H hfree x y hxF
        ((extendedClosedComplexFordRegion_coe H y).mp hy) g hgy)

/-- The actual strict spherical common exterior is contained in the closed one, including infinity. -/
theorem extendedComplexFordRegion_subset_closed (H : Subgroup complexMobiusGroup) :
    extendedComplexFordRegion H⊆extendedClosedComplexFordRegion H := by
  rw [extendedComplexFordRegion_eq]
  rintro x (⟨z,hz,rfl⟩|hInf)
  · exact Or.inl ⟨z,complexFordRegion_subset_closed H hz,rfl⟩
  · exact Or.inr hInf

/-- The general original-domain Ford assertion as a precise boundary-adjusted orbit selector. Connectivity of the common exterior is not assumed. -/
theorem exists_generalFord_fundamentalSet (H : Subgroup complexMobiusGroup)
    (D : Set ExtendedComplex) (ho : IsOpen D)
    (hinv : ∀g : H,∀x∈D,g • x∈D) (hd : DiscreteGroups.IsMobiusDiscontinuousOn H D)
    (hinf : (∞:ExtendedComplex)∈D) (hfree : ∀g : H,g • (∞:ExtendedComplex)=∞→g=1) :
    letI : MulAction H D:=DiscreteGroups.Action.invariantSubsetMulAction D hinv
    ∃F : Set D,DiscreteGroups.Action.IsFundamentalSet H D F ∧
      {x : D | x.val∈extendedComplexFordRegion H}⊆F ∧
      F⊆{x : D | x.val∈extendedClosedComplexFordRegion H} := by
  let : MulAction H D:=DiscreteGroups.Action.invariantSubsetMulAction D hinv
  apply Fuchsian.exists_fundamentalSet_between (G:=H) (X:=D)
    {x : D | x.val∈extendedComplexFordRegion H} {x : D | x.val∈extendedClosedComplexFordRegion H}
    (fun _ hx=>extendedComplexFordRegion_subset_closed H hx)
  · intro x
    obtain ⟨g,hg⟩:=extendedClosedComplexFordRegion_meets_every_orbit H D ho hinv hd hinf hfree x.val x.property
    exact ⟨g,hg.2⟩
  · intro x hx y hy hxy
    obtain ⟨g,hg⟩:=(Quotient.exact hxy : MulAction.orbitRel H D x y)
    apply Subtype.ext
    apply extendedComplexFord_strict_closed_orbit_unique H hfree x.val y.val hx
      (extendedComplexFordRegion_subset_closed H hy) g⁻¹
    have hv:=congrArg Subtype.val hg
    change g • y.val=x.val at hv
    rw [←hv,inv_smul_smul]


/-- The boundary of a genuine non-affine isometric circle has zero ordinary Euclidean area. -/
theorem complexFord_circle_volume_zero (A : Auxiliary.Algebra.SpecialLinear2) (hc : A 1 0≠0) :
    volume {z : ℂ | ‖A 1 0*z+A 1 1‖=1}=0 := by
  have hc0 : ‖A 1 0‖≠0:=norm_ne_zero_iff.mpr hc
  have he : {z : ℂ | ‖A 1 0*z+A 1 1‖=1}=Metric.sphere (-A 1 1/A 1 0) (1/‖A 1 0‖) := by
    ext z
    have hfactor : A 1 0*z+A 1 1=A 1 0*(z-(-A 1 1/A 1 0)) := by field_simp;ring
    simp only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_eq_norm,hfactor,norm_mul]
    rw [eq_div_iff hc0,mul_comm ‖A 1 0‖]
  rw [he]
  exact Measure.addHaar_sphere volume _ _

/-- For an actual discrete original group, closed versus strict common exteriors differ only on a countable union of true isometric circles. -/
theorem complexFord_closed_sdiff_strict_volume_zero (H : Subgroup complexMobiusGroup)
    (hd : IsDiscreteMobiusSubgroup H) : volume (closedComplexFordRegion H\complexFordRegion H)=0 := by
  classical
  let K:=H.comap mobiusSpecialLinearProjection
  let : DiscreteTopology K:=discreteMobius_preimage H hd
  let : Countable K := by
    apply Set.countable_univ_iff.mp
    apply (Set.countable_iUnion (fun n : ℕ=>(DiscreteGroups.MatrixGroups.finite_norm_bounded K n).countable)).mono
    intro A _hA
    obtain ⟨n,hn⟩:=exists_nat_gt (Auxiliary.Algebra.matrixNorm A.val)
    exact mem_iUnion.mpr ⟨n,hn.le⟩
  let F : Set ℂ:=⋃A : {A : K // A.val 1 0≠0},{z : ℂ | ‖A.val.val 1 0*z+A.val.val 1 1‖=1}
  have hF : volume F=0:=measure_iUnion_null (fun A=>complexFord_circle_volume_zero A.val.val A.property)
  apply measure_mono_null _ hF
  rintro z ⟨hz,hnot⟩
  change ¬(∀A : Auxiliary.Algebra.SpecialLinear2,mobiusSpecialLinearProjection A∈H→A 1 0≠0→1<‖A 1 0*z+A 1 1‖) at hnot
  push Not at hnot
  obtain ⟨A,hA,hc,hle⟩:=hnot
  exact mem_iUnion.mpr ⟨⟨⟨A,hA⟩,hc⟩,le_antisymm hle (hz A hA hc)⟩


/-- The precise general original-domain assertion: an actual whole-group orbit selector contains every strict Ford point and differs from it only inside a genuine zero-area boundary set. -/
theorem generalFord_essential_fundamental_region (H : Subgroup complexMobiusGroup)
    (D : Set ExtendedComplex) (ho : IsOpen D)
    (hinv : ∀g : H,∀x∈D,g • x∈D) (hd : DiscreteGroups.IsMobiusDiscontinuousOn H D)
    (hinf : (∞:ExtendedComplex)∈D) (hfree : ∀g : H,g • (∞:ExtendedComplex)=∞→g=1) :
    letI : MulAction H D:=DiscreteGroups.Action.invariantSubsetMulAction D hinv
    ∃F : Set D,DiscreteGroups.Action.IsFundamentalSet H D F ∧
      {x : D | x.val∈extendedComplexFordRegion H}⊆F ∧
      F⊆{x : D | x.val∈extendedClosedComplexFordRegion H} ∧
      volume {z : ℂ | (z:ExtendedComplex)∈Subtype.val '' F ∧ z∉complexFordRegion H}=0 := by
  let : MulAction H D:=DiscreteGroups.Action.invariantSubsetMulAction D hinv
  obtain ⟨F,hF,hstrict,hclosed⟩:=exists_generalFord_fundamentalSet H D ho hinv hd hinf hfree
  refine ⟨F,hF,hstrict,hclosed,?_⟩
  apply measure_mono_null _ (complexFord_closed_sdiff_strict_volume_zero H
    (DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete H D hinv ⟨∞,hinf⟩ hd))
  rintro z ⟨⟨x,hx,hxz⟩,hz⟩
  refine ⟨(extendedClosedComplexFordRegion_coe H z).mp ?_,hz⟩
  rw [←hxz]
  exact hclosed hx

end LowDimensionalTopology.Geometry.Mobius
