module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.DihedralAxisFundamentalDomains
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped OnePoint Pointwise UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Logarithmic radius is continuous on the upper half-plane. -/
theorem continuous_halfPlane_logNorm : Continuous (fun z : ℍ => Real.log ‖(z:ℂ)‖) :=
  UpperHalfPlane.continuous_coe.norm.log (fun z => norm_ne_zero_iff.mpr z.ne_zero)

/-- A compact set meets only finitely many dilation translates of a set with bounded logarithmic radius. -/
theorem HalfPlaneFuchsianGroup.dilation_power_hits_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    (S : Set ℍ) (M : ℝ) (hS : ∀ z ∈ S, |Real.log ‖(z:ℂ)‖| ≤ M)
    (B : Set ℍ) (hB : IsCompact B) :
    letI := P.nativeAction
    {n : ℤ | (((⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩ : H) • ·) '' S ∩ B).Nonempty}.Finite := by
  let nativePowerHitsAction := P.nativeAction
  obtain ⟨C,hC⟩ := hB.bddAbove_image continuous_halfPlane_logNorm.abs.continuousOn
  apply (Set.finite_Icc (⌈(-C-M)/l⌉ : ℤ) ⌊(C+M)/l⌋).subset
  rintro n ⟨_y,⟨x,hx,rfl⟩,hyB⟩
  let a : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩
  have hxbound := abs_le.mp (hS x hx)
  have hybound := abs_le.mp (hC (mem_image_of_mem (fun z : ℍ => |Real.log ‖(z:ℂ)‖|) hyB))
  have hlog := P.dilation_element_logNorm l a n rfl x
  refine ⟨Int.ceil_le.mpr ((div_le_iff₀ hl).mpr ?_),Int.le_floor.mpr ((le_div_iff₀ hl).mpr ?_)⟩ <;> linarith

/-- The cyclic annulus has finitely many closed-tile compact hits for the cyclic dilation group. -/
theorem HalfPlaneFuchsianGroup.dilationAnnulus_compact_hits_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l)
    (hH : H = Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) (B : Set ℍ) (hB :
      IsCompact B) :
    letI := P.nativeAction
    {g : H | ((g • ·) '' closure (dilationAxisAnnulus l) ∩ B).Nonempty}.Finite := by
  let nativeCyclicAnnulusHitsAction := P.nativeAction
  have hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H := by rw [hH];exact Subgroup.mem_zpowers _
  have hS (z : ℍ) (hz : z ∈ closure (dilationAxisAnnulus l)) : |Real.log ‖(z:ℂ)‖| ≤ l := by
    have hh := (mem_closure_dilationAxisAnnulus_iff l hl z).mp hz
    exact abs_le.mpr ⟨by linarith,hh.2⟩
  let J := {n : ℤ | (((⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩ : H) •
    ·) '' closure (dilationAxisAnnulus l) ∩ B).Nonempty}
  have hJ : J.Finite := P.dilation_power_hits_finite l hl hfH _ l hS B hB
  apply (hJ.image (fun n : ℤ => (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH
    n⟩ : H))).subset
  intro g hg
  have hgm : g.val ∈ Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) := by rw [←hH];exact g.property
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp hgm
  have hng : (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩ :
    H) = g := Subtype.ext hn
  refine ⟨n,?_,hng⟩
  change (((⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩ : H) • ·) ''
    closure (dilationAxisAnnulus l) ∩ B).Nonempty
  rw [hng]
  exact hg

/-- An axis half-turn reverses logarithmic radius about its positive-height center. -/
theorem HalfPlaneFuchsianGroup.axis_exchange_logNorm {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (s : H)
    (haxis : s.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (hswap : s.val.val (0:ℂ) = ∞ ∧ s.val.val ∞ = (0:ℂ)) :
    letI := P.nativeAction
    ∃ c : ℝ, ∀ z : ℍ, Real.log ‖((s • z : ℍ):ℂ)‖ = c-Real.log ‖(z:ℂ)‖ := by
  let nativeAxisExchangeLogAction := P.nativeAction
  obtain ⟨r,hr,he⟩ := P.axis_exchange_coe s haxis hswap
  refine ⟨2*Real.log r,fun z => ?_⟩
  rw [he z,norm_div,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
    Real.log_div (pow_ne_zero 2 hr.ne') (norm_ne_zero_iff.mpr z.ne_zero),Real.log_pow]
  norm_num

/-- A compact set meets finitely many closed right-annuli under the cyclic and reversing axis actions. -/
theorem HalfPlaneFuchsianGroup.dihedralAnnulus_compact_hits_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    (s : H) (haxis : s.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (hswap : s.val.val (0:ℂ) = ∞ ∧ s.val.val ∞ = (0:ℂ))
    (hform : ∀ g : H, ∃ n : ℤ, g.val = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n ∨ g.val =
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n*s.val)
    (B : Set ℍ) (hB : IsCompact B) :
    letI := P.nativeAction
    {g : H | ((g • ·) '' closure (dihedralAxisRightAnnulus l) ∩ B).Nonempty}.Finite := by
  let nativeDihedralAnnulusHitsAction := P.nativeAction
  let S := closure (dihedralAxisRightAnnulus l)
  have hS (z : ℍ) (hz : z ∈ S) : |Real.log ‖(z:ℂ)‖| ≤ l := by
    have hz' : z ∈ closure (dilationAxisAnnulus l) := closure_mono inter_subset_left hz
    have hh := (mem_closure_dilationAxisAnnulus_iff l hl z).mp hz'
    exact abs_le.mpr ⟨by linarith,hh.2⟩
  obtain ⟨c,hc⟩ := P.axis_exchange_logNorm s haxis hswap
  have hsS (z : ℍ) (hz : z ∈ (s • ·) '' S) : |Real.log ‖(z:ℂ)‖| ≤ |c|+l := by
    obtain ⟨x,hx,rfl⟩ := hz
    rw [hc]
    exact (abs_sub _ _).trans (by linarith [hS x hx])
  let a (n : ℤ) : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩
  let J := {n : ℤ | (((a n) • ·) '' S ∩ B).Nonempty}
  let K := {n : ℤ | (((a n) • ·) '' ((s • ·) '' S) ∩ B).Nonempty}
  have hJ : J.Finite := P.dilation_power_hits_finite l hl hfH S l hS B hB
  have hK : K.Finite := P.dilation_power_hits_finite l hl hfH _ (|c|+l) hsS B hB
  apply ((hJ.image a).union (hK.image (fun n => a n*s))).subset
  intro g hg
  obtain ⟨n,hn|hn⟩ := hform g
  · have hng : a n = g := Subtype.ext hn.symm
    refine Or.inl ⟨n,?_,hng⟩
    change (((a n) • ·) '' S ∩ B).Nonempty
    rw [hng]
    exact hg
  · have hng : a n*s = g := Subtype.ext hn.symm
    refine Or.inr ⟨n,?_,hng⟩
    obtain ⟨y,⟨x,hx,hxy⟩,hyB⟩ := hg
    change (((a n) • ·) '' ((s • ·) '' S) ∩ B).Nonempty
    refine ⟨y,⟨s • x,mem_image_of_mem _ hx,?_⟩,hyB⟩
    change a n • (s • x) = y
    rw [←mul_smul,hng]
    exact hxy

/-- The full primitive-axis stabilizer has a convex, locally finite annular fundamental domain in both cases. -/
theorem HalfPlaneFuchsianGroup.primitive_dilation_axis_locallyFinite_fundamental
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (l : ℝ) (hl : 0 < l) (hp : IsPrimitive H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    letI := P.axisStabilizerData.nativeAction
    ∃ D : Set ℍ, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) ℍ volume D ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex D ∧ (D = dilationAxisAnnulus l ∨ D =
        dihedralAxisRightAnnulus l) ∧
      ∀ B : Set ℍ, IsCompact B →
        {g : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis | ((g • ·) '' closure D ∩ B).Nonempty}.Finite := by
  let N := P.axisStabilizerData
  let nativeFullAxisLocallyFiniteAction := N.nativeAction
  have hfK : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis :=
    ⟨hp.mem,stableAxisDilation_image_axis l⟩
  rcases P.primitive_dilation_axis_stabilizer l hp with hcyclic | ⟨s,hsK,hs0,hsi,hs2,_hsE,hform⟩
  · exact ⟨dilationAxisAnnulus l,N.dilationAnnulus_fundamental l hl hcyclic,
      dilationAxisAnnulus_hConvex l,Or.inl rfl,N.dilationAnnulus_compact_hits_finite l hl hcyclic⟩
  · let sK : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := ⟨s,hsK⟩
    have hsaxis : sK.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := hsK.2
    have hswap : sK.val.val (0:ℂ) = ∞ ∧ sK.val.val ∞ = (0:ℂ) := ⟨hs0,hsi⟩
    have hword (g : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) :
        ∃ n : ℤ, g.val = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n ∨ g.val = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n*sK.val :=
      (hform g.val).mp g.property
    exact ⟨dihedralAxisRightAnnulus l,N.dihedralAnnulus_fundamental l hl hfK sK hsaxis hswap hs2 hword,
      dihedralAxisRightAnnulus_hConvex l,Or.inr rfl,
      N.dihedralAnnulus_compact_hits_finite l hl hfK sK hsaxis hswap hword⟩

end LowDimensionalTopology.Geometry.Fuchsian
