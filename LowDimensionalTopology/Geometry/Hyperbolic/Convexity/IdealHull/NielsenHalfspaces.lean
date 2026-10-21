/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.ClosedDisk
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Convex.Topology
@[expose] public section
open Set Filter
open scoped Topology RealInnerProductSpace Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- Strict sides of genuine nonconstant real affine hyperplanes enclosing A. -/
def nielsenStrictHalfspaceIntersection (A : Set ℂ) : Set ℂ:=
  {z | ∀f : StrongDual ℝ ℂ,f≠0 → ∀t : ℝ,(∀p∈A,f p≤t) → f z<t}

theorem nielsen_nonzero_functional_surjective (f : StrongDual ℝ ℂ) (hf : f≠0) :
    Function.Surjective f := by
  have hex : ∃v : ℂ,f v≠0:=by
    by_contra h
    push Not at h
    apply hf
    ext v
    exact h v
  obtain ⟨v,hv⟩:=hex
  intro r
  refine ⟨(r/f v) • v,?_⟩
  rw [map_smul]
  change (r/f v)*f v=r
  exact div_mul_cancel₀ r hv

/-- The strict sides are the genuine interior of the closed convex hull; no minimality is built into the definition. -/
theorem nielsen_strictHalfspaces_eq_interior (A : Set ℂ)
    (hInt : (interior (closedConvexHull ℝ A)).Nonempty) :
    nielsenStrictHalfspaceIntersection A=interior (closedConvexHull ℝ A) := by
  ext z
  constructor
  · intro hz
    by_contra hout
    obtain ⟨f,hf,hfA⟩:=geometric_hahn_banach_of_nonempty_interior_point
      (convex_closedConvexHull (𝕜:=ℝ) (s:=A)) hout hInt
    exact (lt_irrefl (f z)) (hz f hf (f z) (fun p hp=>hfA p (subset_closedConvexHull (𝕜:=ℝ) (s:=A) hp)))
  · intro hz f hf t hft
    have hs : closedConvexHull ℝ A⊆f ⁻¹' Iic t:=
      closedConvexHull_min hft ((convex_Iic t).linear_preimage f.toLinearMap)
        (isClosed_Iic.preimage f.continuous)
    have hzI:=interior_mono hs hz
    rw [f.interior_preimage (nielsen_nonzero_functional_surjective f hf),interior_Iic] at hzI
    exact hzI

/-- The separating affine sides may be expressed by actual Euclidean normal vectors. -/
theorem nielsen_strictHalfspaces_mem_iff_inner (A : Set ℂ) (z : ℂ) :
    z∈nielsenStrictHalfspaceIntersection A ↔
      ∀n : ℂ,n≠0 → ∀t : ℝ,(∀p∈A,inner ℝ n p≤t) → inner ℝ n z<t := by
  constructor
  · intro h n hn t ht
    have hf : InnerProductSpace.toDual ℝ ℂ n≠0:=by
      intro he
      apply hn
      have hh:=congrArg (InnerProductSpace.toDual ℝ ℂ).symm he
      simpa using hh
    exact h (InnerProductSpace.toDual ℝ ℂ n) hf t ht
  · intro h f hf t ht
    let n : ℂ:=(InnerProductSpace.toDual ℝ ℂ).symm f
    have hn : n≠0:=by
      intro he
      apply hf
      have hh : InnerProductSpace.toDual ℝ ℂ n=f:=(InnerProductSpace.toDual ℝ ℂ).apply_symm_apply f
      rw [he,map_zero] at hh
      exact hh.symm
    have ht' : ∀p∈A,inner ℝ n p≤t:=by
      intro p hp
      simpa only [n,InnerProductSpace.toDual_symm_apply] using ht p hp
    simpa only [n,InnerProductSpace.toDual_symm_apply] using h n hn t ht'


/-- Three distinct true unit-circle vertices form a genuine noncollinear ideal triangle. -/
def nielsenIdealTriangle (p q r : ℂ) (hp : ‖p‖=1) (hq : ‖q‖=1) (hr : ‖r‖=1)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) : ClosedDiscTriangle where
  a:=Complex.UnitClosedDisc.mk p hp.le
  b:=Complex.UnitClosedDisc.mk q hq.le
  c:=Complex.UnitClosedDisc.mk r hr.le
  noncollinear:=by
    rintro ⟨L,hpL,hqL,hrL⟩
    have hPQ : Complex.UnitClosedDisc.mk p hp.le≠Complex.UnitClosedDisc.mk q hq.le:=by
      intro he
      exact hpq (congrArg (fun z : 𝕔𝔻=>(z : ℂ)) he)
    have he:=L.idealEndpoints_eq_pair_of_closedCarrier
      (Complex.UnitClosedDisc.mk p hp.le) (Complex.UnitClosedDisc.mk q hq.le) hp hq hPQ hpL hqL
    have hrB:=(L.closedCarrier_mem_ideal_iff (Complex.UnitClosedDisc.mk r hr.le) hr).mp hrL
    rw [he] at hrB
    rcases hrB with h | h
    · exact hpr (OnePoint.coe_injective h).symm
    · exact hqr (OnePoint.coe_injective h).symm

/-- Infinitely many actual ideal points force genuine two-dimensional hull interior. -/
theorem nielsen_infinite_unitCircle_hull_interior (A : Set ℂ) (hA : A.Infinite)
    (hsphere : ∀p∈A,‖p‖=1) : (interior (closedConvexHull ℝ A)).Nonempty := by
  obtain ⟨p,hp⟩:=hA.nonempty
  obtain ⟨q,hq,hqNot⟩:=(hA.sdiff (Set.finite_singleton p)).nonempty
  have hqp : q≠p:=by simpa only [Set.mem_singleton_iff] using hqNot
  obtain ⟨r,hr,hrpq⟩:=(hA.sdiff ((Set.finite_singleton q).insert p)).nonempty
  have hpr : p≠r:=by intro he;exact hrpq (Or.inl he.symm)
  have hqr : q≠r:=by intro he;exact hrpq (Or.inr he.symm)
  let T:=nielsenIdealTriangle p q r (hsphere p hp) (hsphere q hq) (hsphere r hr) hqp.symm hpr hqr
  have hpa : closedKleinCoordinate T.a=p:=kleinFormula_norm_one (hsphere p hp)
  have hqb : closedKleinCoordinate T.b=q:=kleinFormula_norm_one (hsphere q hq)
  have hrc : closedKleinCoordinate T.c=r:=kleinFormula_norm_one (hsphere r hr)
  have htri : standardClosedTriangle⊆T.coordinateHomeomorph '' closedConvexHull ℝ A:=by
    have heq : (T.coordinateAffine : ℂ → ℝ × ℝ)=T.coordinateHomeomorph:=rfl
    have hc : Convex ℝ (T.coordinateHomeomorph '' closedConvexHull ℝ A):=by
      rw [←heq]
      exact convex_closedConvexHull.affine_image T.coordinateAffine
    apply standardClosedTriangle_subset_convex hc
    · refine ⟨p,subset_closedConvexHull hp,?_⟩
      rw [←hpa]
      exact T.coordinate_a
    · refine ⟨q,subset_closedConvexHull hq,?_⟩
      rw [←hqb]
      exact T.coordinate_b
    · refine ⟨r,subset_closedConvexHull hr,?_⟩
      rw [←hrc]
      exact T.coordinate_c
  have hInt : (interior (T.coordinateHomeomorph '' closedConvexHull ℝ A)).Nonempty:=
    (show (interior standardClosedTriangle).Nonempty from by
      rw [standardClosedTriangle_interior]
      exact ⟨(1/3,1/3),by norm_num [standardOpenTriangle]⟩).mono (interior_mono htri)
  rw [←T.coordinateHomeomorph.image_interior] at hInt
  exact hInt.of_image


/-- A real supporting line of two distinct ideal points lies strictly above the minimum support of D. -/
theorem nielsen_support_lower_bound {A : Set ℂ} {n : ℂ} {t : ℝ} (hn : n≠0)
    (hpq : ∃p∈A,∃q∈A,p≠q) (hsphere : ∀p∈A,‖p‖=1)
    (hsupport : ∀p∈A,inner ℝ n p≤t) : -‖n‖<t := by
  obtain ⟨p,hp,q,hq,hpq⟩:=hpq
  have hpN:=hsphere p hp
  have hqN:=hsphere q hq
  have hd : 0<‖p-q‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hpq))
  have hplus:=norm_add_sq_real p q
  have hminus:=norm_sub_sq_real p q
  rw [hpN,hqN] at hplus hminus
  have hnorm : ‖p+q‖<2:=by nlinarith [norm_nonneg (p+q)]
  have hnN : 0<‖n‖:=norm_pos_iff.mpr hn
  have hb:=neg_le_of_abs_le (abs_real_inner_le_norm n (p+q))
  rw [inner_add_right] at hb
  nlinarith [hsupport p hp,hsupport q hq]

/-- Every nontrivial Euclidean chord cut is an actual native hyperbolic geodesic. -/
theorem nielsen_exists_discLine_of_cut (n : ℂ) (t : ℝ) (hn : n≠0) (hcut : |t|<‖n‖) :
    ∃L : DiscLine,∀z : 𝔻,z∈L.carrier ↔ inner ℝ n (kleinCoordinate z)=t := by
  have hline : IsDiscHLine {z : 𝔻 | inner ℝ n (kleinCoordinate z)=t}:=by
    apply (isDiscHLine_iff_euclidean _).mpr
    by_cases ht : t=0
    · right
      refine ⟨n,hn,?_⟩
      subst t
      ext z
      change inner ℝ n (kleinFormula (z : ℂ))=0 ↔ inner ℝ (z : ℂ) n=0
      rw [real_inner_comm (kleinFormula (z : ℂ)) n]
      exact (klein_diameter_iff z n).symm
    · left
      let c : ℂ:=t⁻¹ • n
      have hc : 1<‖c‖:=by
        have htpos : 0 < |t|:=abs_pos.mpr ht
        simpa only [c,norm_smul,Real.norm_eq_abs,abs_inv,div_eq_inv_mul] using
          (one_lt_div htpos).mpr hcut
      let r : ℝ:=Real.sqrt (‖c‖^2-1)
      have hrad : 0<‖c‖^2-1:=by nlinarith
      have hr : 0<r:=Real.sqrt_pos.mpr hrad
      have hcr : ‖c‖^2=r^2+1:=by rw [Real.sq_sqrt hrad.le];ring
      refine ⟨c,r,hr,hcr,?_⟩
      ext z
      rw [mem_ofPred_eq,mem_ofPred_eq,klein_circle_iff z c r hr hcr]
      change inner ℝ n (kleinCoordinate z)=t ↔ inner ℝ (kleinCoordinate z) (t⁻¹ • n)=1
      rw [real_inner_smul_right,real_inner_comm n (kleinCoordinate z)]
      constructor
      · intro he
        rw [he,inv_mul_cancel₀ ht]
      · intro he
        have hh:=congrArg (fun x : ℝ=>t*x) he
        field_simp [ht] at hh
        exact hh
  obtain ⟨L,hL⟩:=hline
  exact ⟨L,fun z=>by rw [←hL];rfl⟩

/-- Intersect the strict Klein sides of all genuine geodesic chords with no ideal points of A on the removed side. -/
def nielsenGeodesicHalfspaceIntersection (A : Set ℂ) : Set 𝔻:=
  {z | ∀n : ℂ,n≠0 → ∀t : ℝ,|t|<‖n‖ → (∀p∈A,inner ℝ n p≤t) → inner ℝ n (kleinCoordinate z)<t}

/-- The whole family of genuine geodesic cut sides has the exact closed-hull interior in Klein coordinates. -/
theorem nielsen_geodesicHalfspaces_eq_hullInterior (A : Set ℂ) (hA : A.Infinite)
    (hsphere : ∀p∈A,‖p‖=1) : nielsenGeodesicHalfspaceIntersection A=
      kleinCoordinate ⁻¹' interior (closedConvexHull ℝ A) := by
  have hpq : ∃p∈A,∃q∈A,p≠q:=by
    obtain ⟨p,hp⟩:=hA.nonempty
    obtain ⟨q,hq,hqp⟩:=(hA.sdiff (Set.finite_singleton p)).nonempty
    exact ⟨p,hp,q,hq,fun he=>hqp he.symm⟩
  rw [←nielsen_strictHalfspaces_eq_interior A (nielsen_infinite_unitCircle_hull_interior A hA hsphere)]
  ext z
  rw [mem_preimage,nielsen_strictHalfspaces_mem_iff_inner]
  constructor
  · intro hz n hn t ht
    by_cases htn : t<‖n‖
    · exact hz n hn t (abs_lt.mpr ⟨nielsen_support_lower_bound hn hpq hsphere ht,htn⟩) ht
    · have hinner:=le_abs_self (inner ℝ n (kleinCoordinate z))
      have habs:=abs_real_inner_le_norm n (kleinCoordinate z)
      have hzN : ‖kleinCoordinate z‖<1:=(poincareToKlein z).norm_lt_one
      have hnN : 0<‖n‖:=norm_pos_iff.mpr hn
      have hnorm : ‖n‖*‖kleinCoordinate z‖<‖n‖:=by nlinarith
      exact lt_of_le_of_lt (hinner.trans habs) (hnorm.trans_le (le_of_not_gt htn))
  · intro hz n hn t _ ht
    exact hz n hn t ht


theorem nielsen_geodesicHalfspaces_isOpen (A : Set ℂ) (hA : A.Infinite)
    (hsphere : ∀p∈A,‖p‖=1) : IsOpen (nielsenGeodesicHalfspaceIntersection A) := by
  rw [nielsen_geodesicHalfspaces_eq_hullInterior A hA hsphere]
  exact isOpen_interior.preimage continuous_kleinCoordinate

theorem nielsen_geodesicHalfspaces_convex (A : Set ℂ) (hA : A.Infinite)
    (hsphere : ∀p∈A,‖p‖=1) : DiscHConvex (nielsenGeodesicHalfspaceIntersection A) := by
  apply (discHConvex_iff_klein_convex _).mpr
  rw [nielsen_geodesicHalfspaces_eq_hullInterior A hA hsphere,
    image_preimage_eq_inter_range,range_kleinCoordinate]
  exact convex_closedConvexHull.interior.inter (convex_ball (0 : ℂ) 1)

theorem nielsen_geodesicHalfspaces_nonempty (A : Set ℂ) (hA : A.Infinite)
    (hsphere : ∀p∈A,‖p‖=1) : (nielsenGeodesicHalfspaceIntersection A).Nonempty := by
  have hCB : closedConvexHull ℝ A⊆Metric.closedBall (0 : ℂ) 1:=
    closedConvexHull_min (fun p hp=>by simpa only [mem_closedBall_zero_iff,hsphere p hp] using (le_refl (1 : ℝ)))
      (convex_closedBall (0 : ℂ) 1) Metric.isClosed_closedBall
  obtain ⟨x,hx⟩:=nielsen_infinite_unitCircle_hull_interior A hA hsphere
  have hxB:=interior_mono hCB hx
  rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ)≠0)] at hxB
  obtain ⟨z,hz⟩ : x∈range kleinCoordinate:=range_kleinCoordinate.symm ▸ hxB
  refine ⟨z,?_⟩
  rw [nielsen_geodesicHalfspaces_eq_hullInterior A hA hsphere,mem_preimage,hz]
  exact hx

/-- These cut sides are the actual connected components bounded by the corresponding geodesic. -/
theorem nielsen_geodesicCut_isOpenHalfPlane (n : ℂ) (t : ℝ) (hn : n≠0) (hcut : |t|<‖n‖)
    (z : 𝔻) (hz : inner ℝ n (kleinCoordinate z)<t) :
    ∃L : DiscLine,z∉L.carrier ∧ discKleinCutLt n t=openDiscHalfPlane L z := by
  obtain ⟨L,hL⟩:=nielsen_exists_discLine_of_cut n t hn hcut
  refine ⟨L,?_,(connectedComponentIn_discLine_lt L n t hL z hz).symm⟩
  intro hzL
  exact (lt_irrefl t) (((hL z).mp hzL) ▸ hz)

end
end LowDimensionalTopology.Geometry.Hyperbolic
