/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.ParabolicPencilTransport
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Inversive
noncomputable section

/-- The actual finite portion of a genuine generalized circle in the native disc. -/
def nativeDiscCircleCarrier (C : Mobius.ComplexGeneralizedCircle) : Set 𝔻 :=
  {z | ((z : ℂ) : OnePoint ℂ)∈C.val}

theorem nativeDiscCircleCarrier_cayley_image (C : Mobius.ComplexGeneralizedCircle) :
    nativeDiscCircleCarrier (C.image cayleyMobius)=halfPlaneToDisc '' halfPlaneCircleCarrier C := by
  ext z
  have hp : cayleyMobius.val ((((discToHalfPlane z : ℍ) : ℂ) : OnePoint ℂ))=((z : ℂ) : OnePoint ℂ) := by
    rw [cayleyMobius_apply,extendedCayley_halfPlane,halfPlaneToDisc_discToHalfPlane]
  constructor
  · rintro ⟨w,hw,he⟩
    have he':=cayleyMobius.val.injective (he.trans hp.symm)
    refine ⟨discToHalfPlane z,?_,halfPlaneToDisc_discToHalfPlane z⟩
    change (((discToHalfPlane z : ℍ) : ℂ) : OnePoint ℂ)∈C.val
    rwa [←he']
  · rintro ⟨w,hw,rfl⟩
    exact ⟨((w : ℂ) : OnePoint ℂ),hw,extendedCayley_halfPlane w⟩

theorem halfPlaneCircleCarrier_cayley_inverse_image (C : Mobius.ComplexGeneralizedCircle) :
    halfPlaneCircleCarrier (C.image cayleyMobius⁻¹)=discToHalfPlane '' nativeDiscCircleCarrier C := by
  ext z
  have hp : cayleyMobius.val ((((z : ℍ) : ℂ) : OnePoint ℂ))=
      ((halfPlaneToDisc z : ℂ) : OnePoint ℂ):=extendedCayley_halfPlane z
  constructor
  · rintro ⟨w,hw,he⟩
    have he' : w=((halfPlaneToDisc z : 𝔻) : ℂ) := by
      have hh:=congrArg cayleyMobius.val he
      change cayleyMobius.val (cayleyMobius.val.symm w)=_ at hh
      simpa only [Equiv.apply_symm_apply,hp] using hh
    refine ⟨halfPlaneToDisc z,?_,discToHalfPlane_halfPlaneToDisc z⟩
    change ((halfPlaneToDisc z : ℂ) : OnePoint ℂ)∈C.val
    rwa [←he']
  · rintro ⟨w,hw,rfl⟩
    refine ⟨((w : ℂ) : OnePoint ℂ),hw,?_⟩
    apply cayleyMobius.val.injective
    change cayleyMobius.val (cayleyMobius.val.symm ((w : ℂ) : OnePoint ℂ))=_
    rw [Equiv.apply_symm_apply,cayleyMobius_apply,extendedCayley_halfPlane,halfPlaneToDisc_discToHalfPlane]

theorem cayley_preimage_idealBoundary :
    cayleyMobius.val ⁻¹' extendedDiscIdealBoundary=halfPlaneIdealBoundary := by
  ext z
  exact (idealBoundary_cayley_iff z).symm

theorem cayley_inverse_preimage_idealBoundary :
    (cayleyMobius⁻¹).val ⁻¹' halfPlaneIdealBoundary=extendedDiscIdealBoundary := by
  ext z
  have hh:=idealBoundary_cayley_iff (extendedCayley.symm z)
  change (extendedCayley.symm z∈halfPlaneIdealBoundary) ↔ z∈extendedDiscIdealBoundary
  simpa only [extendedCayley.apply_symm_apply] using hh

/-- Native actual nonempty generalized circles tangent at the designated ideal point. -/
def IsDiscHorocycleAt (w : OnePoint ℂ) (S : Set 𝔻) : Prop :=
  ∃C : Mobius.ComplexGeneralizedCircle,C.val∩extendedDiscIdealBoundary={w} ∧
    S=nativeDiscCircleCarrier C ∧ S.Nonempty

/-- The genuine native pencil uses its actual common ideal end. -/
def discParabolicPencil (w : OnePoint ℂ) : Set DiscLine := {L | w∈L.idealEndpoints}

theorem IsHHorocycleAt.cayley_image {w : OnePoint ℂ} {S : Set ℍ} (hS : IsHHorocycleAt w S) :
    IsDiscHorocycleAt (extendedCayley w) (halfPlaneToDisc '' S) := by
  obtain ⟨C,hC,rfl,hne⟩:=hS
  refine ⟨C.image cayleyMobius,?_,(nativeDiscCircleCarrier_cayley_image C).symm,hne.image halfPlaneToDisc⟩
  change (cayleyMobius.val '' C.val)∩extendedDiscIdealBoundary=_
  rw [←image_inter_preimage,cayley_preimage_idealBoundary,hC,image_singleton]
  rfl

theorem IsDiscHorocycleAt.cayley_inverse_image {w : OnePoint ℂ} {S : Set 𝔻}
    (hS : IsDiscHorocycleAt w S) :
    IsHHorocycleAt (extendedCayley.symm w) (discToHalfPlane '' S) := by
  obtain ⟨C,hC,rfl,hne⟩:=hS
  refine ⟨C.image cayleyMobius⁻¹,?_,(halfPlaneCircleCarrier_cayley_inverse_image C).symm,
    hne.image discToHalfPlane⟩
  change ((cayleyMobius⁻¹).val '' C.val)∩halfPlaneIdealBoundary=_
  rw [←image_inter_preimage,cayley_inverse_preimage_idealBoundary,hC,image_singleton]
  rfl

theorem isDiscHorocycleAt_iff_halfPlane (w : OnePoint ℂ) (S : Set 𝔻) :
    IsDiscHorocycleAt w S ↔ IsHHorocycleAt (extendedCayley.symm w) (discToHalfPlane '' S) := by
  refine ⟨fun h=>h.cayley_inverse_image,?_⟩
  intro h
  have hh:=h.cayley_image
  rwa [extendedCayley.apply_symm_apply,cayley_image_inverse_image] at hh

theorem mem_discParabolicPencil_iff_halfPlane (w : OnePoint ℂ) (L : DiscLine) :
    L∈discParabolicPencil w ↔ L.toHalfPlane∈hParabolicPencil (extendedCayley.symm w) :=
  L.mem_idealEndpoints_iff_halfPlane w

/-- Native P1: every actual point belongs to exactly one actual horocycle at the given ideal end. -/
theorem existsUnique_discHorocycleAt_through (w : OnePoint ℂ) (hw : w∈extendedDiscIdealBoundary) (z : 𝔻) :
    ∃!S : Set 𝔻,IsDiscHorocycleAt w S ∧ z∈S := by
  have hwH : extendedCayley.symm w∈halfPlaneIdealBoundary := by
    apply (idealBoundary_cayley_iff _).mpr
    rwa [extendedCayley.apply_symm_apply]
  obtain ⟨S,⟨hS,hz⟩,hunique⟩:=existsUnique_hHorocycleAt_through (extendedCayley.symm w) hwH (discToHalfPlane z)
  refine ⟨halfPlaneToDisc '' S,⟨?_,discToHalfPlane z,hz,halfPlaneToDisc_discToHalfPlane z⟩,?_⟩
  · have hh:=hS.cayley_image
    rwa [extendedCayley.apply_symm_apply] at hh
  · rintro T ⟨hT,hzT⟩
    have he : discToHalfPlane '' T=S:=hunique _ ⟨hT.cayley_inverse_image,mem_image_of_mem _ hzT⟩
    have hh:=congrArg (fun U : Set ℍ => halfPlaneToDisc '' U) he
    rwa [cayley_image_inverse_image] at hh

/-- Native P2 has no exceptional disc interior point. -/
theorem existsUnique_discParabolicPencil_through (w : OnePoint ℂ) (hw : w∈extendedDiscIdealBoundary) (z : 𝔻) :
    ∃!L : DiscLine,L∈discParabolicPencil w ∧ z∈L.carrier := by
  have hwH : extendedCayley.symm w∈halfPlaneIdealBoundary := by
    apply (idealBoundary_cayley_iff _).mpr
    rwa [extendedCayley.apply_symm_apply]
  obtain ⟨L,⟨hL,hz⟩,hunique⟩:=existsUnique_hParabolicPencil_through (extendedCayley.symm w) hwH (discToHalfPlane z)
  refine ⟨L.toDiscLine,⟨?_,?_⟩,?_⟩
  · rw [mem_discParabolicPencil_iff_halfPlane,L.toDiscLine_toHalfPlane]
    exact hL
  · rw [DiscLine.mem_carrier,L.toDiscLine_toHalfPlane]
    exact hz
  · rintro M ⟨hM,hzM⟩
    apply DiscLine.toHalfPlane_injective
    rw [L.toDiscLine_toHalfPlane]
    exact hunique M.toHalfPlane ⟨(mem_discParabolicPencil_iff_halfPlane w M).mp hM,
      (M.mem_carrier z).mp hzM⟩


/-- Native P3 uses actual complete Euclidean generalized circles and actual normal orthogonality. -/
theorem discHorocycleAt_orthogonal {w : OnePoint ℂ} (hw : w∈extendedDiscIdealBoundary)
    {L : DiscLine} (hL : L∈discParabolicPencil w) {S : Set 𝔻} (hS : IsDiscHorocycleAt w S) :
    ∃C : Mobius.ComplexGeneralizedCircle,S=nativeDiscCircleCarrier C ∧ Mobius.ComplexCirclesOrthogonal L.val C := by
  have hwH : extendedCayley.symm w∈halfPlaneIdealBoundary := by
    apply (idealBoundary_cayley_iff _).mpr
    rwa [extendedCayley.apply_symm_apply]
  obtain ⟨C,hC,ho⟩:=hHorocycleAt_orthogonal hwH
    ((mem_discParabolicPencil_iff_halfPlane w L).mp hL) hS.cayley_inverse_image
  refine ⟨C.image cayleyMobius,?_,?_⟩
  · rw [nativeDiscCircleCarrier_cayley_image,←hC,cayley_image_inverse_image]
  · have he : L.toHalfPlane.extendedCircle.image cayleyMobius=L.val := by
      change L.toHalfPlane.toDiscLine.val=L.val
      rw [L.toHalfPlane_spec]
    rw [←he]
    exact ho.image _ _ _

/-- Native P4 for the actual generalized-circle reflection. -/
theorem discHorocycleAt_reflection {w : OnePoint ℂ} (hw : w∈extendedDiscIdealBoundary)
    {L : DiscLine} (hL : L∈discParabolicPencil w) {S : Set 𝔻} (hS : IsDiscHorocycleAt w S) :
    L.reflection '' S=S := by
  have hwH : extendedCayley.symm w∈halfPlaneIdealBoundary := by
    apply (idealBoundary_cayley_iff _).mpr
    rwa [extendedCayley.apply_symm_apply]
  have hh:=hHorocycleAt_reflection hwH
    ((mem_discParabolicPencil_iff_halfPlane w L).mp hL) hS.cayley_inverse_image
  have he:=congrArg (fun T : Set ℍ => halfPlaneToDisc '' T) hh
  rw [cayley_image_inverse_image] at he
  calc
    L.reflection '' S=halfPlaneToDisc '' (L.toHalfPlane.reflection '' (discToHalfPlane '' S)) := by
      rw [image_image,image_image]
      rfl
    _=S := he

/-- Genuine distance values over actual native curve-point pairs. -/
def discCurvePairDistances (S T : Set 𝔻) : Set ℝ :=
  {d | ∃p∈S,∃q∈T,d=discPathDist p q}

def discCurveDistance (S T : Set 𝔻) : ℝ := sInf (discCurvePairDistances S T)

theorem discCurveDistance_eq_halfPlane (S T : Set 𝔻) :
    discCurveDistance S T=hCurveDistance (discToHalfPlane '' S) (discToHalfPlane '' T) := by
  change sInf (discCurvePairDistances S T)=sInf (hCurvePairDistances (discToHalfPlane '' S) (discToHalfPlane '' T))
  congr 1
  ext d
  constructor
  · rintro ⟨p,hp,q,hq,rfl⟩
    exact ⟨discToHalfPlane p,mem_image_of_mem _ hp,discToHalfPlane q,mem_image_of_mem _ hq,
      discPathDist_eq_halfPlane p q⟩
  · rintro ⟨_,⟨p,hp,rfl⟩,_,⟨q,hq,rfl⟩,rfl⟩
    exact ⟨p,hp,q,hq,(discPathDist_eq_halfPlane p q).symm⟩

/-- Native P5 realizes the true infimum over the actual disc curves. -/
theorem discHorocycleAt_equidistance {w : OnePoint ℂ} (hw : w∈extendedDiscIdealBoundary)
    {S T : Set 𝔻} (hS : IsDiscHorocycleAt w S) (hT : IsDiscHorocycleAt w T) (p : 𝔻) (hp : p∈S) :
    ∃q : 𝔻,q∈T ∧ discPathDist p q=discCurveDistance S T ∧
      ∃L : DiscLine,L∈discParabolicPencil w ∧ p∈L.carrier ∧ q∈L.carrier := by
  have hwH : extendedCayley.symm w∈halfPlaneIdealBoundary := by
    apply (idealBoundary_cayley_iff _).mpr
    rwa [extendedCayley.apply_symm_apply]
  obtain ⟨q,hq,hd,L,hL,hpL,hqL⟩:=hHorocycleAt_equidistance hwH
    hS.cayley_inverse_image hT.cayley_inverse_image (discToHalfPlane p) (mem_image_of_mem _ hp)
  obtain ⟨v,hv,rfl⟩:=hq
  refine ⟨v,hv,?_,L.toDiscLine,?_,?_,?_⟩
  · rw [discPathDist_eq_halfPlane,discCurveDistance_eq_halfPlane]
    exact hd
  · rw [mem_discParabolicPencil_iff_halfPlane,L.toDiscLine_toHalfPlane]
    exact hL
  · rw [DiscLine.mem_carrier,L.toDiscLine_toHalfPlane]
    exact hpL
  · rw [DiscLine.mem_carrier,L.toDiscLine_toHalfPlane]
    exact hqL

theorem exists_common_discHorocycleAt_iff_halfPlane (w : OnePoint ℂ) (a b : 𝔻) :
    (∃S : Set 𝔻,IsDiscHorocycleAt w S ∧ a∈S ∧ b∈S) ↔
      ∃T : Set ℍ,IsHHorocycleAt (extendedCayley.symm w) T ∧ discToHalfPlane a∈T ∧ discToHalfPlane b∈T := by
  constructor
  · rintro ⟨S,hS,ha,hb⟩
    exact ⟨discToHalfPlane '' S,hS.cayley_inverse_image,mem_image_of_mem _ ha,mem_image_of_mem _ hb⟩
  · rintro ⟨T,hT,ha,hb⟩
    refine ⟨halfPlaneToDisc '' T,?_,⟨discToHalfPlane a,ha,halfPlaneToDisc_discToHalfPlane a⟩,
      discToHalfPlane b,hb,halfPlaneToDisc_discToHalfPlane b⟩
    have hh:=hT.cayley_image
    rwa [extendedCayley.apply_symm_apply] at hh

/-- Native P6 retains the genuine perpendicular-bisector construction. -/
theorem discParabolicPencil_perpendicularBisector_iff {w : OnePoint ℂ} (hw : w∈extendedDiscIdealBoundary)
    {a b : 𝔻} (hab : a≠b) {N : DiscLine} (hN : IsDiscPerpendicularBisector N a b) :
    N∈discParabolicPencil w ↔ ∃S : Set 𝔻,IsDiscHorocycleAt w S ∧ a∈S ∧ b∈S := by
  have hwH : extendedCayley.symm w∈halfPlaneIdealBoundary := by
    apply (idealBoundary_cayley_iff _).mpr
    rwa [extendedCayley.apply_symm_apply]
  rw [mem_discParabolicPencil_iff_halfPlane,exists_common_discHorocycleAt_iff_halfPlane]
  exact hParabolicPencil_perpendicularBisector_iff hwH (discToHalfPlane_injective.ne hab)
    ((isDiscPerpendicularBisector_iff_halfPlane N a b).mp hN)


theorem discHorocycle_one_eq_cayley_image_horizontal (r : ℝ) (hr : 0<r) (hr1 : r<1) :
    discHorocycle 1 r=halfPlaneToDisc '' horizontalHorocycle ((1-r)/r) := by
  change frontier (discHorocyclicRegion 1 r)=_
  rw [discHorocyclicRegion_one_eq_cayley_image r hr hr1]
  change frontier (cayleyHomeomorph '' horizontalHorocyclicRegion ((1-r)/r))=_
  rw [←cayleyHomeomorph.image_frontier]
  congr 1
  exact (horizontalHorocycle_eq_actual_boundary _).symm

theorem extendedCayley_symm_one : extendedCayley.symm ((1 : ℂ) : OnePoint ℂ)=∞ := by
  apply extendedCayley.injective
  rw [extendedCayley.apply_symm_apply,extendedCayley_infty]

/-- The intrinsic actual-circle convention agrees with the existing true region-frontier
horocycles, with all positive proper Euclidean radii, at the normalized ideal end. -/
theorem isDiscHorocycleAt_one_iff (S : Set 𝔻) :
    IsDiscHorocycleAt ((1 : ℂ) : OnePoint ℂ) S ↔
      ∃r : ℝ,0<r ∧ r<1 ∧ S=discHorocycle 1 r := by
  constructor
  · intro hS
    have hH:=hS.cayley_inverse_image
    rw [extendedCayley_symm_one] at hH
    obtain ⟨t,ht,he⟩:=(IsHHorocycleAt_infty_iff _).mp hH
    let r:=1/(t+1)
    have hr : 0<r:=by dsimp [r]; positivity
    have hr1 : r<1:=by dsimp [r]; rw [div_lt_one (by positivity)]; linarith
    have he' : (1-r)/r=t:=by dsimp [r]; field_simp; ring
    refine ⟨r,hr,hr1,?_⟩
    rw [discHorocycle_one_eq_cayley_image_horizontal r hr hr1,he',←he,cayley_image_inverse_image]
  · rintro ⟨r,hr,hr1,rfl⟩
    rw [discHorocycle_one_eq_cayley_image_horizontal r hr hr1]
    have hh:=(horizontalHorocycle_isHHorocycleAt ((1-r)/r) (div_pos (sub_pos.mpr hr1) hr)).cayley_image
    rwa [extendedCayley_infty] at hh

def discRotationMobius (u : ℂ) (hu : ‖u‖=1) : Mobius.complexMobiusGroup :=
  Mobius.affineMobius u 0 (norm_ne_zero_iff.mp (by rw [hu]; norm_num))

theorem discRotationMobius_coe (u : ℂ) (hu : ‖u‖=1) (z : ℂ) :
    (discRotationMobius u hu).val (z : OnePoint ℂ)=((u*z : ℂ) : OnePoint ℂ) := by
  rw [discRotationMobius,Mobius.affineMobius_coe]
  change Mobius.affineHomeomorph u 0 _ (z : OnePoint ℂ)=_
  rw [Mobius.affineHomeomorph_coe,add_zero]

theorem discRotationMobius_infty (u : ℂ) (hu : ‖u‖=1) :
    (discRotationMobius u hu).val ∞=∞ := by
  rw [discRotationMobius,Mobius.affineMobius_coe]
  change Mobius.affineHomeomorph u 0 _ ∞=∞
  exact Mobius.affineHomeomorph_infty _ _ _

theorem discRotationMobius_preimage_idealBoundary (u : ℂ) (hu : ‖u‖=1) :
    (discRotationMobius u hu).val ⁻¹' extendedDiscIdealBoundary=extendedDiscIdealBoundary := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [discRotationMobius_infty,extendedDiscIdealBoundary]
  | coe z =>
    rw [mem_preimage,discRotationMobius_coe,coe_mem_extendedDiscIdealBoundary,coe_mem_extendedDiscIdealBoundary,
      norm_mul,hu,one_mul]

theorem nativeDiscCircleCarrier_rotation_image (C : Mobius.ComplexGeneralizedCircle) (u : ℂ) (hu : ‖u‖=1) :
    nativeDiscCircleCarrier (C.image (discRotationMobius u hu))=discUnitRotation u hu '' nativeDiscCircleCarrier C := by
  ext z
  constructor
  · rintro ⟨w,hw,he⟩
    induction w using OnePoint.rec with
    | infty =>
      rw [discRotationMobius_infty] at he
      exact False.elim (OnePoint.coe_ne_infty _ he.symm)
    | coe w =>
      rw [discRotationMobius_coe,OnePoint.coe_eq_coe] at he
      have hwlt : ‖w‖<1 := by
        have hh:=z.norm_lt_one
        rw [←he,norm_mul,hu,one_mul] at hh
        exact hh
      refine ⟨Complex.UnitDisc.mk w hwlt,hw,?_⟩
      apply Subtype.ext
      exact he
  · rintro ⟨w,hw,rfl⟩
    exact ⟨((w : ℂ) : OnePoint ℂ),hw,discRotationMobius_coe u hu w⟩

theorem IsDiscHorocycleAt.rotation_image {w : OnePoint ℂ} {S : Set 𝔻} (hS : IsDiscHorocycleAt w S)
    (u : ℂ) (hu : ‖u‖=1) :
    IsDiscHorocycleAt ((discRotationMobius u hu).val w) (discUnitRotation u hu '' S) := by
  obtain ⟨C,hC,rfl,hne⟩:=hS
  refine ⟨C.image (discRotationMobius u hu),?_,(nativeDiscCircleCarrier_rotation_image C u hu).symm,
    hne.image _⟩
  change ((discRotationMobius u hu).val '' C.val)∩extendedDiscIdealBoundary=_
  rw [←image_inter_preimage,discRotationMobius_preimage_idealBoundary,hC,image_singleton]


theorem unit_mul_conj_eq_one (u : ℂ) (hu : ‖u‖=1) : u*conj u=1 := by
  rw [Complex.mul_conj]
  have he : Complex.normSq u=1:=by rw [Complex.normSq_eq_norm_sq,hu,one_pow]
  exact_mod_cast he

theorem discUnitRotation_inverse_apply (u : ℂ) (hu : ‖u‖=1) (z : 𝔻) :
    discUnitRotation (conj u) (by simpa only [Complex.norm_conj] using hu) (discUnitRotation u hu z)=z := by
  apply Subtype.ext
  change conj u*(u*(z : ℂ))=(z : ℂ)
  rw [←mul_assoc,mul_comm (conj u) u,unit_mul_conj_eq_one u hu,one_mul]

def discUnitRotationHomeomorph (u : ℂ) (hu : ‖u‖=1) : 𝔻 ≃ₜ 𝔻 where
  toFun:=discUnitRotation u hu
  invFun:=discUnitRotation (conj u) (by simpa only [Complex.norm_conj] using hu)
  left_inv:=discUnitRotation_inverse_apply u hu
  right_inv:=by
    intro z
    have hh:=discUnitRotation_inverse_apply (conj u) (by simpa only [Complex.norm_conj] using hu) z
    simpa using hh
  continuous_toFun:=by
    apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun z : 𝔻 => u*(z : ℂ))
    exact continuous_const.mul Complex.UnitDisc.continuous_coe
  continuous_invFun:=by
    apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun z : 𝔻 => conj u*(z : ℂ))
    exact continuous_const.mul Complex.UnitDisc.continuous_coe

theorem discHorocycle_eq_rotation_image (u : ℂ) (hu : ‖u‖=1) (r : ℝ) :
    discHorocycle u r=discUnitRotation u hu '' discHorocycle 1 r := by
  change frontier (discHorocyclicRegion u r)=_
  rw [discHorocyclicRegion_eq_rotation_preimage u hu r]
  change frontier ((discUnitRotationHomeomorph u hu).symm ⁻¹' discHorocyclicRegion 1 r)=_
  rw [←Homeomorph.preimage_frontier,Homeomorph.preimage_symm]
  rfl

/-- Exact full native adapter: the genuine-circle family is precisely the source's actual
boundaries of internally tangent Euclidean discs, with all and only proper positive radii. -/
theorem isDiscHorocycleAt_coe_iff (u : ℂ) (hu : ‖u‖=1) (S : Set 𝔻) :
    IsDiscHorocycleAt (u : OnePoint ℂ) S ↔ ∃r : ℝ,0<r ∧ r<1 ∧ S=discHorocycle u r := by
  constructor
  · intro hS
    have hrot:=hS.rotation_image (conj u) (by simpa only [Complex.norm_conj] using hu)
    rw [discRotationMobius_coe,mul_comm (conj u) u,unit_mul_conj_eq_one u hu] at hrot
    obtain ⟨r,hr,hr1,he⟩:=(isDiscHorocycleAt_one_iff _).mp hrot
    refine ⟨r,hr,hr1,?_⟩
    rw [discHorocycle_eq_rotation_image u hu r,←he,image_image]
    have hf : (fun z : 𝔻 => discUnitRotation u hu
        (discUnitRotation (conj u) (by simpa only [Complex.norm_conj] using hu) z))=id := by
      funext z
      exact (discUnitRotationHomeomorph u hu).apply_symm_apply z
    rw [hf,Set.image_id]
  · rintro ⟨r,hr,hr1,rfl⟩
    have h1 : IsDiscHorocycleAt ((1 : ℂ) : OnePoint ℂ) (discHorocycle 1 r):=
      (isDiscHorocycleAt_one_iff _).mpr ⟨r,hr,hr1,rfl⟩
    have hh:=h1.rotation_image u hu
    rw [discRotationMobius_coe,mul_one,←discHorocycle_eq_rotation_image u hu r] at hh
    exact hh


theorem IsHHorocycleAt.center_mem_idealBoundary {w : OnePoint ℂ} {S : Set ℍ} (hS : IsHHorocycleAt w S) :
    w∈halfPlaneIdealBoundary := by
  obtain ⟨C,hC,_,_⟩:=hS
  have hh : w∈C.val∩halfPlaneIdealBoundary:=by rw [hC]; exact mem_singleton w
  exact hh.2

theorem IsDiscHorocycleAt.center_mem_idealBoundary {w : OnePoint ℂ} {S : Set 𝔻} (hS : IsDiscHorocycleAt w S) :
    w∈extendedDiscIdealBoundary := by
  obtain ⟨C,hC,_,_⟩:=hS
  have hh : w∈C.val∩extendedDiscIdealBoundary:=by rw [hC]; exact mem_singleton w
  exact hh.2

theorem hParabolicPencil_members_parallel {w : OnePoint ℂ} {L M : HalfPlaneLine}
    (hL : L∈hParabolicPencil w) (hM : M∈hParabolicPencil w) (hne : L≠M) : L.Parallel M := by
  refine ⟨hne,w,?_⟩
  ext p
  constructor
  · intro hp
    exact Set.mem_singleton_iff.mpr ((L.idealEndpoints_inter_subsingleton M hne) hp ⟨hL,hM⟩)
  · intro hp
    have he : p=w:=hp
    subst p
    exact ⟨hL,hM⟩

theorem discParabolicPencil_members_parallel {w : OnePoint ℂ} {L M : DiscLine}
    (hL : L∈discParabolicPencil w) (hM : M∈discParabolicPencil w) (hne : L≠M) : L.Parallel M := by
  have hH:=hParabolicPencil_members_parallel ((mem_discParabolicPencil_iff_halfPlane w L).mp hL)
    ((mem_discParabolicPencil_iff_halfPlane w M).mp hM) (DiscLine.toHalfPlane_injective.ne hne)
  refine ⟨hne,w,?_⟩
  have hh : L.toHalfPlane.idealEndpoints∩M.toHalfPlane.idealEndpoints={extendedCayley.symm w}:=by
    ext p
    constructor
    · intro hp
      obtain ⟨v,hv⟩:=hH.2
      have he : p=extendedCayley.symm w:=by
        have hpv : p∈({v} : Set (OnePoint ℂ)):=hv ▸ hp
        have hwv : extendedCayley.symm w∈({v} : Set (OnePoint ℂ)):=hv ▸
          ⟨(mem_discParabolicPencil_iff_halfPlane w L).mp hL,(mem_discParabolicPencil_iff_halfPlane w M).mp hM⟩
        exact (show p=v from hpv).trans (show extendedCayley.symm w=v from hwv).symm
      exact he
    · intro hp
      have he : p=extendedCayley.symm w:=hp
      subst p
      exact ⟨(mem_discParabolicPencil_iff_halfPlane w L).mp hL,(mem_discParabolicPencil_iff_halfPlane w M).mp hM⟩
  rw [L.idealEndpoints_eq_cayley_image,M.idealEndpoints_eq_cayley_image,
    ←image_inter extendedCayley.injective,hh,image_singleton,extendedCayley.apply_symm_apply]

/-- Every intrinsic actual H horocycle is exactly the existing genuine horocyclic-region frontier. -/
theorem IsHHorocycleAt.exists_actual_region {w : OnePoint ℂ} {S : Set ℍ} (hS : IsHHorocycleAt w S) :
    ∃T : Set ℍ,IsHHorocyclicRegion T ∧ S=hHorocycle T := by
  have hD:=hS.cayley_image
  have hwD:=hD.center_mem_idealBoundary
  cases he : extendedCayley w using OnePoint.rec with
  | infty => simp [he,extendedDiscIdealBoundary] at hwD
  | coe u =>
    rw [he,coe_mem_extendedDiscIdealBoundary] at hwD
    rw [he] at hD
    obtain ⟨r,hr,hr1,hcurve⟩:=(isDiscHorocycleAt_coe_iff u hwD _).mp hD
    let T:=discToHalfPlane '' discHorocyclicRegion u r
    refine ⟨T,?_,?_⟩
    · change IsDiscHorocyclicRegion (halfPlaneToDisc '' (discToHalfPlane '' discHorocyclicRegion u r))
      rw [cayley_image_inverse_image]
      exact ⟨u,hwD,r,hr,hr1,rfl⟩
    · apply cayleyHomeomorph.injective.image_injective
      change halfPlaneToDisc '' S=cayleyHomeomorph '' frontier T
      rw [cayleyHomeomorph.image_frontier]
      change halfPlaneToDisc '' S=frontier (halfPlaneToDisc '' (discToHalfPlane '' discHorocyclicRegion u r))
      rw [cayley_image_inverse_image]
      exact hcurve

/-- Conversely, the existing genuine region-frontier horocycles have an actual ideal center. -/
theorem IsHHorocyclicRegion.frontier_isHHorocycle {T : Set ℍ} (hT : IsHHorocyclicRegion T) :
    ∃w : OnePoint ℂ,IsHHorocycleAt w (hHorocycle T) := by
  obtain ⟨u,hu,r,hr,hr1,hregion⟩:=hT
  have hD : IsDiscHorocycleAt (u : OnePoint ℂ) (halfPlaneToDisc '' hHorocycle T) := by
    apply (isDiscHorocycleAt_coe_iff u hu _).mpr
    refine ⟨r,hr,hr1,?_⟩
    change cayleyHomeomorph '' frontier T=frontier (discHorocyclicRegion u r)
    rw [cayleyHomeomorph.image_frontier]
    change frontier (halfPlaneToDisc '' T)=_
    rw [hregion]
  have hh:=hD.cayley_inverse_image
  rw [inverse_cayley_image_image] at hh
  exact ⟨_,hh⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
