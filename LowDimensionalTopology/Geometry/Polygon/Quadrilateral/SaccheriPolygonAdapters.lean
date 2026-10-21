/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HalfPlaneLorentzReflections
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.LambertPolygonAdapters
public import LowDimensionalTopology.Geometry.Polygon.Support.CyclicDiscPolygonSupports
/-! # Actual convex Jordan Saccheri quadrilaterals, including ideal summits -/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Polygon
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc Topology
noncomputable section

theorem CenteredDiscPolygonSupportData.support_normal_proportional {n : ℕ}
    (S : CenteredDiscPolygonSupportData n) (i : Fin n) :
    ∃ k : ℝ,k≠0 ∧ (S.supportLine i).incenterNormal=k • S.normals i ∧
      (S.supportLine i).incenterOffset=k*S.offsets i := by
  let L:=S.supportLine i
  have hn : S.normals i≠0 := by
    intro he
    have hh:=S.normal_norm i
    rw [he,norm_zero] at hh
    norm_num at hh
  have hm : L.incenterNormal≠0 := by
    intro he
    have hh:=L.toHalfPlane.incenterNormal_lorentz_unit
    change ‖L.incenterNormal‖^2-L.incenterOffset^2=1 at hh
    rw [he,norm_zero,zero_pow (by omega : 2≠0)] at hh
    nlinarith only [hh,sq_nonneg L.incenterOffset]
  have hpq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
    i)≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i)) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (S.vertices_injective.ne
      (centeredPolygonSupport_next_ne_self S.three_le i).symm)
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_affine_normals_proportional (S.normals
    i) L.incenterNormal
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
      i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i)))
    (S.offsets i) L.incenterOffset hn hm hpq (S.incident i).1 (S.incident i).2
    (sub_eq_zero.mp ((L.closed_incenter_affine_zero_iff _).mpr (S.incident_mem_support i).1))
    (sub_eq_zero.mp ((L.closed_incenter_affine_zero_iff _).mpr (S.incident_mem_support i).2))

theorem CenteredDiscPolygonSupportData.support_pairing_orthogonal_zero {n : ℕ}
    (S : CenteredDiscPolygonSupportData n) (i : Fin n) (N :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (z : 𝔻)
    (hperp : (S.supportLine i).OrthogonalAt N z) :
    inner ℝ (S.normals i) N.incenterNormal-S.offsets i*N.incenterOffset=0 := by
  obtain ⟨k,hk,hn,ht⟩:=S.support_normal_proportional i
  have hp:=(S.supportLine i).toHalfPlane.normalPairing_orthogonal N.toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)
    (((S.supportLine i).orthogonalAt_iff_halfPlane N z).mp hperp)
  change inner ℝ (S.supportLine i).incenterNormal N.incenterNormal-
    (S.supportLine i).incenterOffset*N.incenterOffset=0 at hp
  rw [hn,ht,real_inner_smul_left] at hp
  have he : k*(inner ℝ (S.normals i) N.incenterNormal-S.offsets i*N.incenterOffset)=0 := by
    nlinarith only [hp]
  exact (mul_eq_zero.mp he).resolve_left hk

theorem closedDiscKleinAffine_neg_of_between (n : ℂ) (t : ℝ) (p q z : 𝕔𝔻)
    (hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine n t p=0) (hz :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine n t z<0)
    (hseg : z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine n t q<0 := by
  have hm:=mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hseg
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment] at hm
  rcases hm with ⟨a,b,ha,hb,hab,he⟩
  have hv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine n t z=a*_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine n t p+b*_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine n t q := by
    unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine
    rw [← he,inner_add_right,inner_smul_right,inner_smul_right]
    linear_combination t*hab
  rw [hp,mul_zero,zero_add] at hv
  by_contra hq
  have hq':=le_of_not_gt hq
  exact (not_lt_of_ge (hv.symm ▸ mul_nonneg hb hq')) hz

def LambertQuadrilateral.saccheriOriginalCut (Q : LambertQuadrilateral) (i : Fin 4) (p : 𝕔𝔻) : ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (Q.polygonUnitNormal i) (Q.polygonUnitOffset
    i) p

theorem LambertQuadrilateral.saccheriOriginalCut_incident (Q : LambertQuadrilateral) (i : Fin 4) :
    Q.saccheriOriginalCut i (Q.polygonVertices i)=0 ∧
      Q.saccheriOriginalCut i (Q.polygonVertices (finRotate 4 i))=0 :=
  ⟨sub_eq_zero.mpr (Q.polygonSupportData.incident i).1,
    sub_eq_zero.mpr (Q.polygonSupportData.incident i).2⟩

theorem LambertQuadrilateral.saccheriOriginalCut_nonincident (Q : LambertQuadrilateral) (i j : Fin 4)
    (hji : j≠i) (hjn : j≠finRotate 4 i) : Q.saccheriOriginalCut i (Q.polygonVertices j)<0 :=
  sub_neg.mpr (Q.polygonSupportData.nonincident i j hji hjn)

theorem LambertQuadrilateral.saccheri_side_pairing_zero (Q : LambertQuadrilateral) (i : Fin 4)
    (hi : i=0 ∨ i=2) :
    inner ℝ (Q.polygonUnitNormal i) Q.left.incenterNormal-Q.polygonUnitOffset i*Q.left.incenterOffset=0 := by
  rcases hi with rfl|rfl
  · apply Q.polygonSupportData.support_pairing_orthogonal_zero 0 Q.left Q.d
    rw [Q.polygonSupportLine_eq]
    exact ⟨Q.angle_d.2.1,Q.angle_d.1,(real_inner_comm _ _).trans Q.angle_d.2.2⟩
  · apply Q.polygonSupportData.support_pairing_orthogonal_zero 2 Q.left Q.a
    rw [Q.polygonSupportLine_eq]
    exact Q.angle_a

theorem LambertQuadrilateral.saccheriOriginalCut_side_reflection (Q : LambertQuadrilateral)
    (i : Fin 4) (hi : i=0 ∨ i=2) (p : 𝕔𝔻) :
    Q.left.reflectionAffineDenominator p*
        Q.saccheriOriginalCut i (Q.left.closedReflectionIsometry.closedMap p)=Q.saccheriOriginalCut i p := by
  have h:=Q.left.closedAffine_reflection_general (Q.polygonUnitNormal i) (Q.polygonUnitOffset i) p
  simpa only [LambertQuadrilateral.saccheriOriginalCut,Q.saccheri_side_pairing_zero i
    hi,mul_zero,zero_mul,sub_zero] using h

theorem LambertQuadrilateral.saccheri_right_cut_reflected_base_neg (Q : LambertQuadrilateral) :
    Q.saccheriOriginalCut 3 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (Q.left.reflection Q.b))<0 := by
  have hp:= (Q.saccheriOriginalCut_incident 3).1
  have hz:=Q.saccheriOriginalCut_nonincident 3 2 (by decide) (by decide)
  change Q.saccheriOriginalCut 3 Q.corner.c=0 at hp
  rw [Q.vertex_b] at hp
  change Q.saccheriOriginalCut 3 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.a)<0 at hz
  exact closedDiscKleinAffine_neg_of_between _ _ _ _ _ hp hz
    (Q.left.reflection_perpendicular_midpoint Q.bottom Q.a Q.b
      ⟨Q.angle_a.2.1,Q.angle_a.1,(real_inner_comm _ _).trans Q.angle_a.2.2⟩
      Q.angle_b.1 Q.a_ne_b.symm).1


theorem LambertQuadrilateral.saccheri_left_affine_multiple (Q : LambertQuadrilateral) :
    ∃ k : ℝ,k≠0 ∧ ∀ p : 𝕔𝔻,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine Q.left.incenterNormal Q.left.incenterOffset p=k*Q.saccheriOriginalCut 1 p := by
  obtain ⟨k,hk,hn,ht⟩:=Q.polygonSupportData.support_normal_proportional 1
  rw [Q.polygonSupportLine_eq] at hn ht
  refine ⟨k,hk,?_⟩
  intro p
  change Q.left.incenterNormal=k • Q.polygonUnitNormal 1 at hn
  change Q.left.incenterOffset=k*Q.polygonUnitOffset 1 at ht
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine,hn,ht,real_inner_smul_left,LambertQuadrilateral.saccheriOriginalCut]
  ring

theorem LambertQuadrilateral.saccheri_left_affine_product_pos (Q : LambertQuadrilateral) :
    0<_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine Q.left.incenterNormal Q.left.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine Q.left.incenterNormal Q.left.incenterOffset Q.corner.a := by
  obtain ⟨k,hk,hm⟩:=Q.saccheri_left_affine_multiple
  have hB:=Q.saccheriOriginalCut_nonincident 1 3 (by decide) (by decide)
  have hC:=Q.saccheriOriginalCut_nonincident 1 0 (by decide) (by decide)
  change Q.saccheriOriginalCut 1 Q.corner.c<0 at hB
  rw [Q.vertex_b] at hB
  change Q.saccheriOriginalCut 1 Q.corner.a<0 at hC
  rw [hm,hm,mul_mul_mul_comm]
  exact mul_pos (mul_self_pos.mpr hk) (mul_pos_of_neg_of_neg hB hC)

def LambertQuadrilateral.saccheriReflectedRightCut (Q : LambertQuadrilateral) (p : 𝕔𝔻) : ℝ :=
  Q.saccheriOriginalCut 3 p-
    2*(inner ℝ (Q.polygonUnitNormal 3) Q.left.incenterNormal-Q.polygonUnitOffset 3*Q.left.incenterOffset)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine Q.left.incenterNormal Q.left.incenterOffset p

theorem LambertQuadrilateral.saccheriReflectedRightCut_eq (Q : LambertQuadrilateral) (p : 𝕔𝔻) :
    Q.saccheriReflectedRightCut p=Q.left.reflectionAffineDenominator p*
      Q.saccheriOriginalCut 3 (Q.left.closedReflectionIsometry.closedMap p) :=
  (Q.left.closedAffine_reflection_general (Q.polygonUnitNormal 3) (Q.polygonUnitOffset 3) p).symm

theorem LambertQuadrilateral.saccheriReflectedRightCut_base_neg (Q : LambertQuadrilateral) :
    Q.saccheriReflectedRightCut (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b)<0 := by
  rw [Q.saccheriReflectedRightCut_eq,Q.left.closedReflectionIsometry.finite_commutes]
  exact mul_neg_of_pos_of_neg (Q.left.reflectionAffineDenominator_pos _) Q.saccheri_right_cut_reflected_base_neg

theorem LambertQuadrilateral.saccheriReflectedRightCut_summit_neg (Q : LambertQuadrilateral) :
    Q.saccheriReflectedRightCut Q.corner.a<0 := by
  have hC:=(Q.saccheriOriginalCut_incident 3).2
  have hB:=(Q.saccheriOriginalCut_incident 3).1
  change Q.saccheriOriginalCut 3 Q.corner.a=0 at hC
  change Q.saccheriOriginalCut 3 Q.corner.c=0 at hB
  rw [Q.vertex_b] at hB
  have hp:=Q.saccheriReflectedRightCut_base_neg
  unfold LambertQuadrilateral.saccheriReflectedRightCut at hp ⊢
  rw [hB,zero_sub,neg_neg_iff_pos] at hp
  rw [hC,zero_sub,neg_neg_iff_pos]
  have hn:=Q.saccheri_left_affine_product_pos
  rcases mul_pos_iff.mp hp with ⟨ha,hb⟩|⟨ha,hb⟩
  · exact mul_pos ha ((mul_pos_iff_of_pos_left hb).mp hn)
  · exact mul_pos_of_neg_of_neg ha (by nlinarith only [hn,hb] : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine Q.left.incenterNormal Q.left.incenterOffset Q.corner.a<0)

theorem LambertQuadrilateral.saccheri_right_cut_reflected_summit_neg (Q : LambertQuadrilateral) :
    Q.saccheriOriginalCut 3 (Q.left.closedReflectionIsometry.closedMap Q.corner.a)<0 := by
  have hp:=Q.saccheriReflectedRightCut_summit_neg
  rw [Q.saccheriReflectedRightCut_eq] at hp
  have hd:=Q.left.reflectionAffineDenominator_pos Q.corner.a
  nlinarith only [hd,hp]


theorem LambertQuadrilateral.saccheriOriginalCut_side_reflection_zero (Q : LambertQuadrilateral)
    (i : Fin 4) (hi : i=0 ∨ i=2) (p : 𝕔𝔻) :
    Q.saccheriOriginalCut i (Q.left.closedReflectionIsometry.closedMap p)=0 ↔ Q.saccheriOriginalCut i p=0 := by
  rw [← Q.saccheriOriginalCut_side_reflection i hi p,mul_eq_zero]
  simp only [(Q.left.reflectionAffineDenominator_pos p).ne',false_or]

theorem LambertQuadrilateral.saccheriOriginalCut_side_reflection_neg (Q : LambertQuadrilateral)
    (i : Fin 4) (hi : i=0 ∨ i=2) (p : 𝕔𝔻) :
    Q.saccheriOriginalCut i (Q.left.closedReflectionIsometry.closedMap p)<0 ↔ Q.saccheriOriginalCut i p<0 := by
  rw [← Q.saccheriOriginalCut_side_reflection i hi p]
  exact ⟨mul_neg_of_pos_of_neg (Q.left.reflectionAffineDenominator_pos p),
    fun h => neg_of_mul_neg_right h (Q.left.reflectionAffineDenominator_pos p).le⟩

theorem LambertQuadrilateral.saccheriVertices_closed_reflection (Q : LambertQuadrilateral) :
    Q.saccheriVertices=![_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b,
      Q.left.closedReflectionIsometry.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        Q.b),
      Q.left.closedReflectionIsometry.closedMap Q.corner.a,Q.corner.a] := by
  rw [Q.left.closedReflectionIsometry.finite_commutes]
  rfl

def LambertQuadrilateral.saccheriCut (Q : LambertQuadrilateral) : Fin 4 → 𝕔𝔻 → ℝ :=
  ![Q.saccheriOriginalCut 2,Q.saccheriReflectedRightCut,Q.saccheriOriginalCut 0,Q.saccheriOriginalCut 3]

theorem LambertQuadrilateral.saccheriCut_incident (Q : LambertQuadrilateral) (i : Fin 4) :
    Q.saccheriCut i (Q.saccheriVertices i)=0 ∧
      Q.saccheriCut i (Q.saccheriVertices (finRotate 4 i))=0 := by
  have hC:=(Q.saccheriOriginalCut_incident 0).1
  have hB:=(Q.saccheriOriginalCut_incident 2).2
  have hRB:=(Q.saccheriOriginalCut_incident 3).1
  have hRC:=(Q.saccheriOriginalCut_incident 3).2
  change Q.saccheriOriginalCut 0 Q.corner.a=0 at hC
  change Q.saccheriOriginalCut 2 Q.corner.c=0 at hB
  change Q.saccheriOriginalCut 3 Q.corner.c=0 at hRB
  change Q.saccheriOriginalCut 3 Q.corner.a=0 at hRC
  rw [Q.vertex_b] at hB hRB
  have hB':=(Q.saccheriOriginalCut_side_reflection_zero 2 (Or.inr rfl) _).mpr hB
  have hC':=(Q.saccheriOriginalCut_side_reflection_zero 0 (Or.inl rfl) _).mpr hC
  have hRB' : Q.saccheriReflectedRightCut (Q.left.closedReflectionIsometry.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b))=0 := by
    rw [Q.saccheriReflectedRightCut_eq,Q.left.closedReflectionIsometry_involutive,hRB,mul_zero]
  have hRC' : Q.saccheriReflectedRightCut (Q.left.closedReflectionIsometry.closedMap Q.corner.a)=0 := by
    rw [Q.saccheriReflectedRightCut_eq,Q.left.closedReflectionIsometry_involutive,hRC,mul_zero]
  have hn : ∀ j : Fin 4,finRotate 4 j=j+1 := by decide
  rw [hn,Q.saccheriVertices_closed_reflection]
  fin_cases i
  · exact ⟨hB,hB'⟩
  · exact ⟨hRB',hRC'⟩
  · exact ⟨hC',hC⟩
  · exact ⟨hRC,hRB⟩

theorem LambertQuadrilateral.saccheriCut_nonincident (Q : LambertQuadrilateral) (i j : Fin 4)
    (hji : j≠i) (hjn : j≠finRotate 4 i) : Q.saccheriCut i (Q.saccheriVertices j)<0 := by
  have hKC:=Q.saccheriOriginalCut_nonincident 2 0 (by decide) (by decide)
  have hMB:=Q.saccheriOriginalCut_nonincident 0 3 (by decide) (by decide)
  change Q.saccheriOriginalCut 2 Q.corner.a<0 at hKC
  change Q.saccheriOriginalCut 0 Q.corner.c<0 at hMB
  rw [Q.vertex_b] at hMB
  have hKC':=(Q.saccheriOriginalCut_side_reflection_neg 2 (Or.inr rfl) _).mpr hKC
  have hMB':=(Q.saccheriOriginalCut_side_reflection_neg 0 (Or.inl rfl) _).mpr hMB
  have hGB:=Q.saccheriReflectedRightCut_base_neg
  have hGC:=Q.saccheriReflectedRightCut_summit_neg
  have hRB':=Q.saccheri_right_cut_reflected_base_neg
  have hmap:=Q.left.closedReflectionIsometry.finite_commutes Q.b
  change Q.left.closedReflectionIsometry.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    Q.b)=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (Q.left.reflection Q.b) at hmap
  rw [← hmap] at hRB'
  have hRC':=Q.saccheri_right_cut_reflected_summit_neg
  have hn : ∀ k : Fin 4,finRotate 4 k=k+1 := by decide
  rw [hn] at hjn
  rw [Q.saccheriVertices_closed_reflection]
  fin_cases i <;> fin_cases j <;> norm_num [LambertQuadrilateral.saccheriCut] at *
  all_goals assumption

def LambertQuadrilateral.saccheriRawNormal (Q : LambertQuadrilateral) : Fin 4 → ℂ :=
  ![Q.polygonUnitNormal 2,
    Q.polygonUnitNormal 3-
      (2*(inner ℝ (Q.polygonUnitNormal 3) Q.left.incenterNormal-Q.polygonUnitOffset 3*Q.left.incenterOffset)) •
        Q.left.incenterNormal,
    Q.polygonUnitNormal 0,Q.polygonUnitNormal 3]

def LambertQuadrilateral.saccheriRawOffset (Q : LambertQuadrilateral) : Fin 4 → ℝ :=
  ![Q.polygonUnitOffset 2,
    Q.polygonUnitOffset 3-
      2*(inner ℝ (Q.polygonUnitNormal 3) Q.left.incenterNormal-Q.polygonUnitOffset 3*Q.left.incenterOffset)*
        Q.left.incenterOffset,
    Q.polygonUnitOffset 0,Q.polygonUnitOffset 3]

theorem LambertQuadrilateral.saccheriCut_eq_affine (Q : LambertQuadrilateral) (i : Fin 4) (p : 𝕔𝔻) :
    Q.saccheriCut i p=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (Q.saccheriRawNormal i) (Q.saccheriRawOffset i) p := by
  fin_cases i <;>
    simp only [LambertQuadrilateral.saccheriCut,LambertQuadrilateral.saccheriRawNormal,LambertQuadrilateral.saccheriRawOffset,Matrix.cons_val_zero',Matrix.cons_val_succ',
      LambertQuadrilateral.saccheriOriginalCut,LambertQuadrilateral.saccheriReflectedRightCut,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine,inner_sub_left,real_inner_smul_left]
  ring

theorem LambertQuadrilateral.saccheriRawNormal_ne_zero (Q : LambertQuadrilateral) (i : Fin 4) :
    Q.saccheriRawNormal i≠0 := by
  have he:=(Q.saccheriCut_incident i).1
  have hl:=Q.saccheriCut_nonincident i (i+2) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
  rw [Q.saccheriCut_eq_affine] at he hl
  intro hn
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine,hn,inner_zero_left,zero_sub] at he hl
  linarith only [he,hl]

def LambertQuadrilateral.saccheriUnitNormal (Q : LambertQuadrilateral) (i : Fin 4) : ℂ :=
  ‖Q.saccheriRawNormal i‖⁻¹ • Q.saccheriRawNormal i

def LambertQuadrilateral.saccheriUnitOffset (Q : LambertQuadrilateral) (i : Fin 4) : ℝ :=
  Q.saccheriRawOffset i/‖Q.saccheriRawNormal i‖

theorem LambertQuadrilateral.saccheriUnitNormal_norm (Q : LambertQuadrilateral) (i : Fin 4) :
    ‖Q.saccheriUnitNormal i‖=1 := by
  have hn:=norm_pos_iff.mpr (Q.saccheriRawNormal_ne_zero i)
  rw [LambertQuadrilateral.saccheriUnitNormal,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀
    hn.ne']

theorem LambertQuadrilateral.saccheriUnitCut (Q : LambertQuadrilateral) (i : Fin 4) (p : 𝕔𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (Q.saccheriUnitNormal
      i) (Q.saccheriUnitOffset i) p=
      Q.saccheriCut i p/‖Q.saccheriRawNormal i‖ := by
  rw [Q.saccheriCut_eq_affine]
  simp only [LambertQuadrilateral.saccheriUnitNormal,LambertQuadrilateral.saccheriUnitOffset,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine,real_inner_smul_left,
    inv_mul_eq_div,sub_div]

def LambertQuadrilateral.saccheriSupportData (Q : LambertQuadrilateral) : CyclicDiscPolygonSupportData 4 where
  three_le:=by decide
  vertices:=Q.saccheriVertices
  vertices_injective:=Q.saccheriVertices_injective
  normals:=Q.saccheriUnitNormal
  normal_norm:=Q.saccheriUnitNormal_norm
  offsets:=Q.saccheriUnitOffset
  incident i:=by
    constructor
    all_goals
      apply sub_eq_zero.mp
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (Q.saccheriUnitNormal
        i) (Q.saccheriUnitOffset i) _=0
      rw [Q.saccheriUnitCut]
    · rw [(Q.saccheriCut_incident i).1,zero_div]
    · rw [(Q.saccheriCut_incident i).2,zero_div]
  nonincident i j hji hjn:=by
    apply sub_neg.mp
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine (Q.saccheriUnitNormal
      i) (Q.saccheriUnitOffset i) _<0
    rw [Q.saccheriUnitCut]
    exact div_neg_of_neg_of_pos (Q.saccheriCut_nonincident i j hji hjn)
      (norm_pos_iff.mpr (Q.saccheriRawNormal_ne_zero i))

def LambertQuadrilateral.saccheriDiscPolygon (Q : LambertQuadrilateral) : DiscPolygon 4 :=
  Q.saccheriSupportData.toDiscPolygon

theorem LambertQuadrilateral.saccheriDiscPolygon_isConvex (Q : LambertQuadrilateral) :
    Q.saccheriDiscPolygon.IsConvex := Q.saccheriSupportData.toDiscPolygon_isConvex


theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.alpha_eq_of_adjacent_pair (T U :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (ha : U.a=T.a) (hp : ({U.b,U.c} : Set 𝕔𝔻)={T.b,T.c}) : U.alpha=T.alpha := by
  have hb : U.b=T.b ∨ U.b=T.c := by
    have hm : U.b∈({U.b,U.c} : Set 𝕔𝔻) := by simp
    rw [hp] at hm
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm
  have hc : U.c=T.b ∨ U.c=T.c := by
    have hm : U.c∈({U.b,U.c} : Set 𝕔𝔻) := by simp
    rw [hp] at hm
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm
  rcases hb with hb|hb
  · have hc' : U.c=T.c := hc.resolve_left (by intro he;exact U.b_ne_c (hb.trans he.symm))
    have he : U=T := by
      cases U
      cases T
      simp_all only
    exact congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.alpha he
  · have hc' : U.c=T.b := hc.resolve_right (by intro he;exact U.b_ne_c (hb.trans he.symm))
    exact T.alpha_eq_of_swapped_neighbors U ha hb hc'

theorem LambertQuadrilateral.saccheriDiscPolygon_vertices (Q : LambertQuadrilateral) :
    Q.saccheriDiscPolygon.vertices=Q.saccheriVertices := rfl

theorem LambertQuadrilateral.saccheriDiscPolygon_angles (Q : LambertQuadrilateral) (i : Fin 4) :
    Q.saccheriDiscPolygon.angle i=if i=0 ∨ i=1 then Real.pi/2 else Q.angle := by
  change Q.saccheriSupportData.toDiscPolygon.angle i=_
  rw [Q.saccheriSupportData.toDiscPolygon_angle]
  rw [← Q.saccheriCorner_angles i]
  let S:=Q.saccheriSupportData.toCenteredData
  apply (S.cornerTriangle i).alpha_eq_of_adjacent_pair (Q.saccheriCorner i) ?_ ?_ |>.symm
  · exact (Q.saccheriCorner_vertices i).1
  · rw [(Q.saccheriCorner_vertices i).2]
    have hprev : (finRotate 4).symm i=i-1 := by fin_cases i <;> decide
    have hnext : finRotate 4 i=i+1 := by fin_cases i <;> decide
    change ({Q.saccheriVertices (i-1),Q.saccheriVertices (i+1)} : Set 𝕔𝔻)=
      {Q.saccheriVertices ((finRotate 4).symm i),Q.saccheriVertices (finRotate 4 i)}
    rw [hprev,hnext]

theorem LambertQuadrilateral.saccheriDiscPolygon_legs_equal (Q : LambertQuadrilateral) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (Q.saccheriDiscPolygon.vertices
      0) (Q.saccheriDiscPolygon.vertices 3)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (Q.saccheriDiscPolygon.vertices
        1) (Q.saccheriDiscPolygon.vertices 2) :=
  Q.saccheri_legs_equal


/-- Three genuine numerical right angles on an arbitrary actual Jordan quadrilateral. -/
def DiscPolygon.IsLambert (P : DiscPolygon 4) : Prop :=
  P.angle 1=Real.pi/2 ∧ P.angle 2=Real.pi/2 ∧ P.angle 3=Real.pi/2

/-- Two genuine right base angles and equal genuine finite or ideal legs. -/
def DiscPolygon.IsSaccheri (P : DiscPolygon 4) : Prop :=
  P.angle 0=Real.pi/2 ∧ P.angle 1=Real.pi/2 ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices 0) (P.vertices 3)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (P.vertices 1) (P.vertices 2)

theorem LambertQuadrilateral.toDiscPolygon_isLambert (Q : LambertQuadrilateral) :
    Q.toDiscPolygon.IsLambert :=
  ⟨Q.toDiscPolygon_angle_one,Q.toDiscPolygon_angle_two,Q.toDiscPolygon_angle_three⟩

theorem LambertQuadrilateral.saccheriDiscPolygon_isSaccheri (Q : LambertQuadrilateral) :
    Q.saccheriDiscPolygon.IsSaccheri := by
  refine ⟨?_,?_,Q.saccheriDiscPolygon_legs_equal⟩
  · exact (Q.saccheriDiscPolygon_angles 0).trans (ite_eq_left (Or.inl rfl))
  · exact (Q.saccheriDiscPolygon_angles 1).trans (ite_eq_left (Or.inr rfl))

theorem exists_saccheriDiscPolygon_angle (φ : ℝ) (hφ : φ∈Ico (0 : ℝ) (Real.pi/2)) :
    ∃ P : DiscPolygon 4,P.IsSaccheri ∧ P.IsConvex ∧ P.angle 2=φ ∧ P.angle 3=φ := by
  let Q:=lambertQuadrilateralOfAngle φ hφ
  refine ⟨Q.saccheriDiscPolygon,Q.saccheriDiscPolygon_isSaccheri,Q.saccheriDiscPolygon_isConvex,?_,?_⟩
  · rw [Q.saccheriDiscPolygon_angles,ite_eq_right (by decide),lambertQuadrilateralOfAngle_angle φ hφ]
  · rw [Q.saccheriDiscPolygon_angles,ite_eq_right (by decide),lambertQuadrilateralOfAngle_angle φ hφ]

end
end LowDimensionalTopology.Geometry.Polygon
