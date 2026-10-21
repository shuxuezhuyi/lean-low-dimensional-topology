/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Ford.ComplexFordRegions
public import LowDimensionalTopology.Geometry.Mobius.Algebraic.OrbitCrossRatioPolynomials
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonIdealBoundary
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology OnePoint UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The exact two-point metric comparison has a polynomial expression continuous up to the actual ideal circle. -/
theorem disc_distance_le_crossmultiply (z a b : 𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z a ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z b ↔
      ‖(z:ℂ)-a‖^2*(1-‖(b:ℂ)‖^2) ≤ ‖(z:ℂ)-b‖^2*(1-‖(a:ℂ)‖^2) := by
  have hz : 0 < 1-‖(z:ℂ)‖^2 := sub_pos.mpr z.sq_norm_lt_one
  have ha : 0 < 1-‖(a:ℂ)‖^2 := sub_pos.mpr a.sq_norm_lt_one
  have hb : 0 < 1-‖(b:ℂ)‖^2 := sub_pos.mpr b.sq_norm_lt_one
  have he : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z
    a) ≤ Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z b) ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z a ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z b := by
    rw [Real.cosh_le_cosh,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,
      abs_of_nonneg dist_nonneg,abs_of_nonneg dist_nonneg]
  rw [←he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_cosh_distance,_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_cosh_distance]
  rw [add_le_add_iff_left,div_le_div_iff₀ (mul_pos hz ha) (mul_pos hz hb)]
  have hL : 2*‖(z:ℂ)-a‖^2*((1-‖(z:ℂ)‖^2)*(1-‖(b:ℂ)‖^2))=
      (2*(1-‖(z:ℂ)‖^2))*(‖(z:ℂ)-a‖^2*(1-‖(b:ℂ)‖^2)) := by ring
  have hR : 2*‖(z:ℂ)-b‖^2*((1-‖(z:ℂ)‖^2)*(1-‖(a:ℂ)‖^2))=
      (2*(1-‖(z:ℂ)‖^2))*(‖(z:ℂ)-b‖^2*(1-‖(a:ℂ)‖^2)) := by ring
  rw [hL,hR,mul_le_mul_iff_right₀ (mul_pos zero_lt_two hz)]

/-- Metric comparison along actual disc points extends continuously to a genuine ideal accumulation point. -/
theorem disc_ideal_poisson_le (a b : 𝔻) (ξ : ℂ) (hunit : ‖ξ‖=1) (S : Set 𝔻)
    (hcl : ξ∈closure (((↑) : 𝔻→ℂ) '' S))
    (hle : ∀z∈S,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z
      a≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z b) :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel b ξ ≤ _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel a ξ := by
  have hcont : IsClosed {z : ℂ | ‖z-a‖^2*(1-‖(b:ℂ)‖^2) ≤ ‖z-b‖^2*(1-‖(a:ℂ)‖^2)} :=
    isClosed_le (((continuous_id.sub continuous_const).norm.pow 2).mul continuous_const)
      (((continuous_id.sub continuous_const).norm.pow 2).mul continuous_const)
  have hc : ‖ξ-a‖^2*(1-‖(b:ℂ)‖^2) ≤ ‖ξ-b‖^2*(1-‖(a:ℂ)‖^2) := by
    apply closure_minimal (t:={z : ℂ | ‖z-a‖^2*(1-‖(b:ℂ)‖^2) ≤ ‖z-b‖^2*(1-‖(a:ℂ)‖^2)}) ?_ hcont hcl
    rintro _ ⟨z,hz,rfl⟩
    exact (disc_distance_le_crossmultiply z a b).mp (hle z hz)
  have hda : 0 < ‖(a:ℂ)-ξ‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr
    (fun he => (ne_of_lt a.norm_lt_one) (he.symm ▸ hunit))))
  have hdb : 0 < ‖(b:ℂ)-ξ‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr
    (fun he => (ne_of_lt b.norm_lt_one) (he.symm ▸ hunit))))
  rw [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel,_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel,div_le_div_iff₀ hdb hda]
  rw [norm_sub_rev ξ (a:ℂ),norm_sub_rev ξ (b:ℂ)] at hc
  linarith only [hc]

/-- A true ideal accumulation point of the original Dirichlet polygon maximizes the actual Poisson weight along the whole orbit of the center. -/
theorem dirichlet_ideal_poisson_max {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (ξ : ℂ)
    (hξ : ξ∈fuchsianPolygonIdealBoundary P (dirichletDomain P w)) (g : H) :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate (g • w)) ξ ≤ _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) ξ := by
  obtain ⟨hcl,hunit⟩:=(mem_fuchsianPolygonIdealBoundary _ _ _).mp hξ
  apply disc_ideal_poisson_le (P.finiteCoordinate w) (P.finiteCoordinate (g • w)) ξ hunit
    (P.finiteCoordinate '' dirichletDomain P w)
  · simpa only [image_image] using hcl
  · rintro _ ⟨z,hz,rfl⟩
    rw [←P.hyperbolicDist_eq_discPathDist z w,←P.hyperbolicDist_eq_discPathDist z (g • w)]
    exact closure_dirichletDomain_le P w (subset_closure hz) g

/-- Actual boundary transport and genuine Poisson covariance for an original disc-group element. -/
theorem UnitDiscFuchsianGroup.poisson_covariance {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (ξ η : ℂ) (hξ : ‖ξ‖=1)
    (himage : g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃κ : ℝ, 0<κ ∧ ∀w : P.domain.carrier,
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate (g • w)) η*κ=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) ξ := by
  obtain ⟨A,hA⟩:=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection_surjective g.val
  obtain ⟨hdet,_hd,hform⟩:=_root_.LowDimensionalTopology.Geometry.Mobius.complexFord_disc_coefficients A (by rw [hA];exact P.image_eq g)
  have hform' : g.val.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation (A 0 0) (A 1 0) hdet := by rw [←hA];exact hform
  have hη : _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap (A 0 0) (A 1 0) ξ=η := by
    apply OnePoint.coe_injective
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation_of_closedDisc _ _ _ hdet
      hξ.le,←hform']
    exact himage
  refine ⟨‖deriv (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap (A 0 0) (A 1 0)) ξ‖,
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_deriv_norm_pos hdet (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_den_ne_zero hdet hξ.le),?_⟩
  intro w
  have hw:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel_covariance hdet (P.finiteCoordinate w).norm_lt_one hξ
  rw [hη] at hw
  rw [P.finite_smul g _ _ hdet hform']
  exact hw

/-- Two literal ideal-cycle points force equality of two genuine, transported boundary Poisson weights. -/
theorem dirichlet_ideal_pair_poisson_equal {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) (ξ η : ℂ)
    (hξ : ξ∈fuchsianPolygonIdealBoundary P (dirichletDomain P w))
    (hη : η∈fuchsianPolygonIdealBoundary P (dirichletDomain P w))
    (himage : g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃κ : ℝ,0<κ ∧ _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) ξ=
      κ*_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) η := by
  obtain ⟨κ,hκ,hcov⟩:=P.poisson_covariance g ξ η
    ((mem_fuchsianPolygonIdealBoundary _ _ _).mp hξ).2 himage
  refine ⟨κ,hκ,le_antisymm ?_ ?_⟩
  · rw [←hcov w,mul_comm κ]
    exact mul_le_mul_of_nonneg_right (dirichlet_ideal_poisson_max P w η hη g) hκ.le
  · have hc:=hcov (g⁻¹ • w)
    rw [smul_inv_smul,mul_comm] at hc
    rw [hc]
    exact dirichlet_ideal_poisson_max P w ξ hξ g⁻¹

/-- Distinct actual ideal points have different rational boundary Cayley poles; no proportional Poisson-weight equality can persist on a positive-area set. -/
theorem UnitDiscFuchsianGroup.poisson_equal_area_zero {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (ξ η : ℂ) (hξ : ‖ξ‖=1) (hη : ‖η‖=1)
    (hne : ξ≠η) (κ : ℝ) :
    P.area {w | _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) ξ=
      κ*_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) η}=0 := by
  let q : Polynomial ℂ := (Polynomial.C ξ-Polynomial.X)*(Polynomial.C η-Polynomial.X)
  let p : Polynomial ℂ := Polynomial.C Complex.I*
    ((Polynomial.C ξ+Polynomial.X)*(Polynomial.C η-Polynomial.X)-
      Polynomial.C (κ:ℂ)*(Polynomial.C η+Polynomial.X)*(Polynomial.C ξ-Polynomial.X))
  have hξ0 : ξ≠0 := by intro he;rw [he,norm_zero] at hξ;norm_num at hξ
  have hq : q≠0 := mul_ne_zero
    (sub_ne_zero.mpr (Polynomial.X_ne_C ξ).symm) (sub_ne_zero.mpr (Polynomial.X_ne_C η).symm)
  have hn : ¬∃c : ℂ,p=Polynomial.C c*q := by
    rintro ⟨c,hc⟩
    have hh:=congrArg (Polynomial.eval ξ) hc
    have hpp : p.eval ξ=Complex.I*(2*ξ*(η-ξ)) := by
      simp only [p,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,sub_self,mul_zero,sub_zero]
      ring
    have hqq : q.eval ξ=0 := by simp [q]
    rw [hpp,Polynomial.eval_mul,Polynomial.eval_C,hqq,mul_zero] at hh
    exact mul_ne_zero Complex.I_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hξ0) (sub_ne_zero.mpr hne.symm)) hh
  apply measure_mono_null _ (P.rational_real_locus_area_zero p q hq hn)
  intro w hw
  let z : ℂ:=P.finiteCoordinate w
  have hzξ:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.unitBoundary_sub_ne_zero (P.finiteCoordinate
    w).norm_lt_one hξ
  have hzη:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.unitBoundary_sub_ne_zero (P.finiteCoordinate
    w).norm_lt_one hη
  have hzξ' : ξ-z≠0:=hzξ
  have hzη' : η-z≠0:=hzη
  have hid : p.eval z/q.eval z=Complex.I*(_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.boundaryCayley ξ z-(κ:ℂ)*_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.boundaryCayley η z) := by
    simp only [p,q,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_add,
      Polynomial.eval_C,Polynomial.eval_X]
    dsimp [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.boundaryCayley]
    field_simp [hzξ',hzη',mul_ne_zero hzξ' hzη']
  change (p.eval z/q.eval z).im=0
  rw [hid]
  change _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel z ξ=κ*_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel z η at hw
  rw [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel_eq_re_boundaryCayley _ hξ,
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel_eq_re_boundaryCayley _ hη] at hw
  simp only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,
    zero_add,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,sub_zero]
  exact sub_eq_zero.mpr hw


/-- A canonical scalar for the actual boundary-weight covariance, fixed independently of the varying Dirichlet center. -/
def idealPoissonFactor {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (g : H) (ξ η : ℂ) : ℝ := _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate P.origin) ξ /
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate (g • P.origin)) η

theorem idealPoissonFactor_pos_covariance {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (ξ η : ℂ) (hξ : ‖ξ‖=1) (hη : ‖η‖=1)
    (himage : g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    0 < idealPoissonFactor P g ξ η ∧ ∀w : P.domain.carrier,
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate (g •
        w)) η*idealPoissonFactor P g ξ η=
        _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) ξ := by
  obtain ⟨κ,hκ,hcov⟩:=P.poisson_covariance g ξ η hξ himage
  have hpos:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel_pos (P.finiteCoordinate (g •
    P.origin)).norm_lt_one hη
  have he : idealPoissonFactor P g ξ η=κ := by
    unfold idealPoissonFactor
    apply (div_eq_iff hpos.ne').mpr
    rw [mul_comm]
    exact (hcov P.origin).symm
  rw [he]
  exact ⟨hκ,hcov⟩

/-- The equal-weight locus attached to a literal ideal-cycle pair uses a scalar independent of the center. -/
theorem dirichlet_ideal_pair_poisson_factor {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) (ξ η : ℂ)
    (hξ : ξ∈fuchsianPolygonIdealBoundary P (dirichletDomain P w))
    (hη : η∈fuchsianPolygonIdealBoundary P (dirichletDomain P w))
    (himage : g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) ξ=
      idealPoissonFactor P g ξ η*_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) η := by
  obtain ⟨hκ,hcov⟩:=idealPoissonFactor_pos_covariance P g ξ η
    ((mem_fuchsianPolygonIdealBoundary _ _ _).mp hξ).2
    ((mem_fuchsianPolygonIdealBoundary _ _ _).mp hη).2 himage
  apply le_antisymm
  · rw [←hcov w,mul_comm (idealPoissonFactor P g ξ η)]
    exact mul_le_mul_of_nonneg_right (dirichlet_ideal_poisson_max P w η hη g) hκ.le
  · have hc:=hcov (g⁻¹ • w)
    rw [smul_inv_smul,mul_comm] at hc
    rw [hc]
    exact dirichlet_ideal_poisson_max P w ξ hξ g⁻¹

end LowDimensionalTopology.Geometry.Fuchsian
