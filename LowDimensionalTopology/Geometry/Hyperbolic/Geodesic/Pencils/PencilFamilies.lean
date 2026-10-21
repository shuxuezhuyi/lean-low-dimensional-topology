/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.NativeHyperbolicPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.NativeEllipticPencils
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Inversive
noncomputable section

/-- The three actual geometric pencil types, with genuine ideal, interior, or axis data. -/
abbrev HGeodesicPencil := {w : OnePoint ℂ // w∈halfPlaneIdealBoundary} ⊕ (ℍ ⊕ HalfPlaneLine)

def HGeodesicPencil.parabolic (w : OnePoint ℂ) (hw : w∈halfPlaneIdealBoundary) : HGeodesicPencil := .inl ⟨w,hw⟩

def HGeodesicPencil.elliptic (p : ℍ) : HGeodesicPencil := .inr (.inl p)

def HGeodesicPencil.hyperbolic (axis : HalfPlaneLine) : HGeodesicPencil := .inr (.inr axis)

def HGeodesicPencil.lines : HGeodesicPencil → Set HalfPlaneLine
  | .inl w => hParabolicPencil w.val
  | .inr (.inl p) => hEllipticPencil p
  | .inr (.inr axis) => hHyperbolicPencil axis

def HGeodesicPencil.curves : HGeodesicPencil → Set (Set ℍ)
  | .inl w => {S | IsHHorocycleAt w.val S}
  | .inr (.inl p) => hMetricCircleFamily p
  | .inr (.inr axis) => {S | IsHHypercycleBranch axis S}

/-- The genuine elliptic center is the single exceptional point for regular curve and line incidence. -/
def HGeodesicPencil.Exceptional : HGeodesicPencil → ℍ → Prop
  | .inl _,_ => False
  | .inr (.inl p),z => z=p
  | .inr (.inr _),_ => False

/-- Corrected regular-curve P1, including its explicitly necessary elliptic-center exception. -/
theorem HGeodesicPencil.existsUnique_curve_through (P : HGeodesicPencil) (z : ℍ) (hz : ¬P.Exceptional z) :
    ∃!S : Set ℍ,S∈P.curves ∧ z∈S := by
  rcases P with w | p | axis
  · exact existsUnique_hHorocycleAt_through w.val w.property z
  · exact existsUnique_hMetricCircle_through hz
  · exact existsUnique_hHypercycleBranch_through axis z

/-- Original P2 with at most the single actual elliptic-center exception. -/
theorem HGeodesicPencil.existsUnique_line_through (P : HGeodesicPencil) (z : ℍ) (hz : ¬P.Exceptional z) :
    ∃!L : HalfPlaneLine,L∈P.lines ∧ z∈L.carrier := by
  rcases P with w | p | axis
  · exact existsUnique_hParabolicPencil_through w.val w.property z
  · exact existsUnique_hEllipticPencil_through hz
  · exact existsUnique_hHyperbolicPencil_through axis z

theorem HGeodesicPencil.exists_regular_point_on_line (P : HGeodesicPencil) (L : HalfPlaneLine) :
    ∃z : ℍ,z∈L.carrier ∧ ¬P.Exceptional z := by
  obtain ⟨a,b,ha,hb,hab⟩:=L.exists_two_points
  rcases P with w | p | axis
  · exact ⟨a,ha,fun h=>h⟩
  · by_cases he : a=p
    · refine ⟨b,hb,?_⟩
      change b≠p
      intro hbp
      exact hab (he.trans hbp.symm)
    · exact ⟨a,ha,he⟩
  · exact ⟨a,ha,fun h=>h⟩

/-- P4 is invariance under the actual native reflection in every genuine pencil line. -/
theorem HGeodesicPencil.reflection_curve (P : HGeodesicPencil) {L : HalfPlaneLine} (hL : L∈P.lines)
    {S : Set ℍ} (hS : S∈P.curves) : L.reflection '' S=S := by
  rcases P with w | p | axis
  · exact hHorocycleAt_reflection w.property hL hS
  · obtain ⟨r,hr,rfl⟩:=hS
    exact hMetricCircle_reflection p r L hL
  · exact hHypercycleBranch_reflection axis hL hS

/-- P5 uses the actual infimum over all genuine curve-point pairs in every geometric type. -/
theorem HGeodesicPencil.curves_equidistant (P : HGeodesicPencil) {S T : Set ℍ}
    (hS : S∈P.curves) (hT : T∈P.curves) (z : ℍ) (hz : z∈S) :
    ∃w : ℍ,w∈T ∧ dist z w=hCurveDistance S T ∧
      ∃L : HalfPlaneLine,L∈P.lines ∧ z∈L.carrier ∧ w∈L.carrier := by
  rcases P with p | p | axis
  · exact hHorocycleAt_equidistance p.property hS hT z hz
  · obtain ⟨r,hr,rfl⟩:=hS
    obtain ⟨s,hs,rfl⟩:=hT
    obtain ⟨w,hw,hd,_,L,hL,hzL,hwL⟩:=hMetricCircle_equidistance p r s hr hs.le z hz
    exact ⟨w,hw,hd,L,hL,hzL,hwL⟩
  · exact hHypercycleBranch_equidistance axis hS hT z hz

/-- Every genuine pencil geodesic actually meets each complementary curve inside H. -/
theorem HGeodesicPencil.line_meets_curve (P : HGeodesicPencil) {L : HalfPlaneLine} (hL : L∈P.lines)
    {S : Set ℍ} (hS : S∈P.curves) : (L.carrier∩S).Nonempty := by
  obtain ⟨z,hzL,hz⟩:=P.exists_regular_point_on_line L
  obtain ⟨T,⟨hT,hzT⟩,huniqueT⟩:=P.existsUnique_curve_through z hz
  obtain ⟨w,hw,hd,M,hM,hzM,hwM⟩:=P.curves_equidistant hT hS z hzT
  obtain ⟨N,hN,huniqueN⟩:=P.existsUnique_line_through z hz
  have he : M=L:=(huniqueN M ⟨hM,hzM⟩).trans (huniqueN L ⟨hL,hzL⟩).symm
  exact ⟨w,he ▸ hwM,hw⟩

/-- P3 includes actual H incidence and genuine Euclidean generalized-circle normal orthogonality. -/
theorem HGeodesicPencil.line_orthogonal_curve (P : HGeodesicPencil) {L : HalfPlaneLine} (hL : L∈P.lines)
    {S : Set ℍ} (hS : S∈P.curves) :
    ∃C : Mobius.ComplexGeneralizedCircle,S=halfPlaneCircleCarrier C ∧
      Mobius.ComplexCirclesOrthogonal L.extendedCircle C ∧ (L.carrier∩S).Nonempty := by
  have hmeet:=P.line_meets_curve hL hS
  rcases P with w | p | axis
  · obtain ⟨C,hC,ho⟩:=hHorocycleAt_orthogonal w.property hL hS
    exact ⟨C,hC,ho,hmeet⟩
  · obtain ⟨r,hr,rfl⟩:=hS
    obtain ⟨C,hC,ho⟩:=hMetricCircle_orthogonal p r hr L hL
    exact ⟨C,hC,ho,hmeet⟩
  · obtain ⟨C,hC,ho⟩:=hHypercycleBranch_orthogonal axis hL hS
    exact ⟨C,hC,ho,hmeet⟩

/-- P6 always refers to the actual geometric perpendicular bisector of distinct actual points. -/
theorem HGeodesicPencil.perpendicularBisector_iff (P : HGeodesicPencil) {a b : ℍ} (hab : a≠b)
    {N : HalfPlaneLine} (hN : IsHPerpendicularBisector N a b) :
    N∈P.lines ↔ ∃S∈P.curves,a∈S ∧ b∈S := by
  rcases P with w | p | axis
  · exact hParabolicPencil_perpendicularBisector_iff w.property hab hN
  · exact hEllipticPencil_perpendicularBisector_iff p hab hN
  · exact hHyperbolicPencil_perpendicularBisector_iff axis hab hN

/-- Two distinct actual generating geodesics of a genuine geometric pencil. -/
def HGeodesicPencil.GeneratedBy (P : HGeodesicPencil) (L M : HalfPlaneLine) : Prop :=
  L∈P.lines ∧ M∈P.lines ∧ L≠M

/-- Corrected P7: actual whole-line containment and nonnegative nonzero weights give exactly the actual pencil. -/
theorem HGeodesicPencil.GeneratedBy.ratioLine_iff {P : HGeodesicPencil} {L M : HalfPlaneLine}
    (h : P.GeneratedBy L M) (N : HalfPlaneLine) : N∈P.lines ↔ L.IsDistanceRatioLine M N := by
  obtain ⟨hL,hM,hne⟩:=h
  rcases P with w | p | axis
  · exact (L.parallel_isDistanceRatioLine_iff M (hParabolicPencil_members_parallel hL hM hne) w.val hL hM N).symm
  · exact (L.intersecting_isDistanceRatioLine_iff M (hEllipticPencil_members_intersecting p hL hM hne) p hL hM N).symm
  · exact (L.disjoint_isDistanceRatioLine_iff M (hHyperbolicPencil_members_hDisjoint axis hL hM hne) axis hL hM N).symm

/-- Every pair of distinct actual geodesics generates one of the three genuine geometric pencil types. -/
theorem exists_hGeodesicPencil_generatedBy (L M : HalfPlaneLine) (hne : L≠M) :
    ∃P : HGeodesicPencil,P.GeneratedBy L M := by
  rcases L.classification M hne with hp | hi | hd
  · obtain ⟨w,hw⟩:=hp.2
    have hwm : w∈L.idealEndpoints∩M.idealEndpoints:=by rw [hw]; exact mem_singleton w
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.parabolic w hwm.1.2,hwm.1,hwm.2,hne⟩
  · obtain ⟨p,hpL,hpM⟩:=hi.2.2
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.elliptic p,hpL,hpM,hne⟩
  · obtain ⟨axis,⟨hL,hM⟩,_⟩:=L.existsUnique_commonOrthogonal M hd
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.hyperbolic axis,hL,hM,hne⟩

/-- Every geometric pencil has two distinct actual generating lines; P7 is never vacuous. -/
theorem HGeodesicPencil.exists_generators (P : HGeodesicPencil) :
    ∃L M : HalfPlaneLine,P.GeneratedBy L M := by
  rcases P with w | p | axis
  · obtain ⟨g,hg,he⟩:=exists_hParabolicChart w.val w.property
    refine ⟨(HalfPlaneLine.vertical 0).realGLMap g,(HalfPlaneLine.vertical 1).realGLMap g,?_,?_,?_⟩
    · change _∈hParabolicPencil w.val
      rw [←he]
      exact (mem_hParabolicPencil_chart_iff g hg _).mpr ⟨0,rfl⟩
    · change _∈hParabolicPencil w.val
      rw [←he]
      exact (mem_hParabolicPencil_chart_iff g hg _).mpr ⟨1,rfl⟩
    · apply (HalfPlaneLine.realGLMap_injective g).ne
      intro h
      have he : (0 : ℝ)=1:=HalfPlaneLine.vertical.inj h
      norm_num at he
  · refine ⟨HalfPlaneLine.vertical p.re,HalfPlaneLine.circle p.re p.im p.im_pos,rfl,?_,?_⟩
    · apply norm_sub_real_eq_of_sq p.im_pos
      ring
    · intro h
      cases h
  · obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
    refine ⟨(HalfPlaneLine.circle 0 1 (by norm_num)).realGLMap g,
      (HalfPlaneLine.circle 0 2 (by norm_num)).realGLMap g,?_,?_,?_⟩
    · exact (mem_hHyperbolicPencil_chart_iff g _).mpr ⟨1,by norm_num,rfl⟩
    · exact (mem_hHyperbolicPencil_chart_iff g _).mpr ⟨2,by norm_num,rfl⟩
    · apply (HalfPlaneLine.realGLMap_injective g).ne
      intro h
      have he : (1 : ℝ)=2:=(HalfPlaneLine.circle.inj h).2
      norm_num at he

/-- The full type classification is witnessed by two genuine lines of exactly the prescribed kind. -/
theorem HGeodesicPencil.GeneratedBy.classification {P : HGeodesicPencil} {L M : HalfPlaneLine}
    (h : P.GeneratedBy L M) :
    (∃w hw,P=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.parabolic w hw ∧ L.Parallel M) ∨
    (∃p,P=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.elliptic p ∧ L.Intersecting M) ∨
    (∃axis,P=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.hyperbolic axis ∧ L.HDisjoint M) := by
  obtain ⟨hL,hM,hne⟩:=h
  rcases P with w | p | axis
  · exact Or.inl ⟨w.val,w.property,rfl,hParabolicPencil_members_parallel hL hM hne⟩
  · exact Or.inr (Or.inl ⟨p,rfl,hEllipticPencil_members_intersecting p hL hM hne⟩)
  · exact Or.inr (Or.inr ⟨axis,rfl,hHyperbolicPencil_members_hDisjoint axis hL hM hne⟩)

/-- The native disc version uses genuine boundary points, interior centers and actual disc axes. -/
abbrev DiscGeodesicPencil := {w : OnePoint ℂ // w∈extendedDiscIdealBoundary} ⊕ (𝔻 ⊕ DiscLine)

def DiscGeodesicPencil.parabolic (w : OnePoint ℂ) (hw : w∈extendedDiscIdealBoundary) : DiscGeodesicPencil := .inl ⟨w,hw⟩
def DiscGeodesicPencil.elliptic (p : 𝔻) : DiscGeodesicPencil := .inr (.inl p)
def DiscGeodesicPencil.hyperbolic (axis : DiscLine) : DiscGeodesicPencil := .inr (.inr axis)

def DiscGeodesicPencil.lines : DiscGeodesicPencil → Set DiscLine
  | .inl w => discParabolicPencil w.val
  | .inr (.inl p) => discEllipticPencil p
  | .inr (.inr axis) => discHyperbolicPencil axis

def DiscGeodesicPencil.curves : DiscGeodesicPencil → Set (Set 𝔻)
  | .inl w => {S | IsDiscHorocycleAt w.val S}
  | .inr (.inl p) => discMetricCircleFamily p
  | .inr (.inr axis) => {S | IsDiscHypercycleBranch axis S}

def DiscGeodesicPencil.Exceptional : DiscGeodesicPencil → 𝔻 → Prop
  | .inl _,_ => False
  | .inr (.inl p),z => z=p
  | .inr (.inr _),_ => False

theorem DiscGeodesicPencil.existsUnique_curve_through (P : DiscGeodesicPencil) (z : 𝔻) (hz : ¬P.Exceptional z) :
    ∃!S : Set 𝔻,S∈P.curves ∧ z∈S := by
  rcases P with w | p | axis
  · exact existsUnique_discHorocycleAt_through w.val w.property z
  · exact existsUnique_discMetricCircle_through hz
  · exact existsUnique_discHypercycleBranch_through axis z

theorem DiscGeodesicPencil.existsUnique_line_through (P : DiscGeodesicPencil) (z : 𝔻) (hz : ¬P.Exceptional z) :
    ∃!L : DiscLine,L∈P.lines ∧ z∈L.carrier := by
  rcases P with w | p | axis
  · exact existsUnique_discParabolicPencil_through w.val w.property z
  · exact existsUnique_discEllipticPencil_through hz
  · exact existsUnique_discHyperbolicPencil_through axis z

theorem DiscGeodesicPencil.exists_regular_point_on_line (P : DiscGeodesicPencil) (L : DiscLine) :
    ∃z : 𝔻,z∈L.carrier ∧ ¬P.Exceptional z := by
  obtain ⟨a,b,ha,hb,hab⟩:=L.toHalfPlane.exists_two_points
  have haD : halfPlaneToDisc a∈L.carrier:=by
    rw [L.mem_carrier,discToHalfPlane_halfPlaneToDisc]
    exact ha
  have hbD : halfPlaneToDisc b∈L.carrier:=by
    rw [L.mem_carrier,discToHalfPlane_halfPlaneToDisc]
    exact hb
  have habD : halfPlaneToDisc a≠halfPlaneToDisc b:=cayleyHomeomorph.injective.ne hab
  rcases P with w | p | axis
  · exact ⟨halfPlaneToDisc a,haD,fun h=>h⟩
  · by_cases he : halfPlaneToDisc a=p
    · refine ⟨halfPlaneToDisc b,hbD,?_⟩
      change halfPlaneToDisc b≠p
      intro hbP
      exact habD (he.trans hbP.symm)
    · exact ⟨halfPlaneToDisc a,haD,he⟩
  · exact ⟨halfPlaneToDisc a,haD,fun h=>h⟩

theorem DiscGeodesicPencil.reflection_curve (P : DiscGeodesicPencil) {L : DiscLine} (hL : L∈P.lines)
    {S : Set 𝔻} (hS : S∈P.curves) : L.reflection '' S=S := by
  rcases P with w | p | axis
  · exact discHorocycleAt_reflection w.property hL hS
  · obtain ⟨r,hr,rfl⟩:=hS
    exact discMetricCircle_reflection p r L hL
  · exact discHypercycleBranch_reflection axis hL hS

theorem DiscGeodesicPencil.curves_equidistant (P : DiscGeodesicPencil) {S T : Set 𝔻}
    (hS : S∈P.curves) (hT : T∈P.curves) (z : 𝔻) (hz : z∈S) :
    ∃w : 𝔻,w∈T ∧ discPathDist z w=discCurveDistance S T ∧
      ∃L : DiscLine,L∈P.lines ∧ z∈L.carrier ∧ w∈L.carrier := by
  rcases P with p | p | axis
  · exact discHorocycleAt_equidistance p.property hS hT z hz
  · obtain ⟨r,hr,rfl⟩:=hS
    obtain ⟨s,hs,rfl⟩:=hT
    obtain ⟨w,hw,hd,_,L,hL,hzL,hwL⟩:=discMetricCircle_equidistance p r s hr hs.le z hz
    exact ⟨w,hw,hd,L,hL,hzL,hwL⟩
  · exact discHypercycleBranch_equidistance axis hS hT z hz

theorem DiscGeodesicPencil.line_meets_curve (P : DiscGeodesicPencil) {L : DiscLine} (hL : L∈P.lines)
    {S : Set 𝔻} (hS : S∈P.curves) : (L.carrier∩S).Nonempty := by
  obtain ⟨z,hzL,hz⟩:=P.exists_regular_point_on_line L
  obtain ⟨T,⟨hT,hzT⟩,_⟩:=P.existsUnique_curve_through z hz
  obtain ⟨w,hw,_,M,hM,hzM,hwM⟩:=P.curves_equidistant hT hS z hzT
  obtain ⟨N,_,huniqueN⟩:=P.existsUnique_line_through z hz
  have he : M=L:=(huniqueN M ⟨hM,hzM⟩).trans (huniqueN L ⟨hL,hzL⟩).symm
  exact ⟨w,he ▸ hwM,hw⟩

theorem DiscGeodesicPencil.line_orthogonal_curve (P : DiscGeodesicPencil) {L : DiscLine} (hL : L∈P.lines)
    {S : Set 𝔻} (hS : S∈P.curves) :
    ∃C : Mobius.ComplexGeneralizedCircle,S=nativeDiscCircleCarrier C ∧
      Mobius.ComplexCirclesOrthogonal L.val C ∧ (L.carrier∩S).Nonempty := by
  have hmeet:=P.line_meets_curve hL hS
  rcases P with w | p | axis
  · obtain ⟨C,hC,ho⟩:=discHorocycleAt_orthogonal w.property hL hS
    exact ⟨C,hC,ho,hmeet⟩
  · obtain ⟨r,hr,rfl⟩:=hS
    obtain ⟨C,hC,ho⟩:=discMetricCircle_orthogonal p r hr L hL
    exact ⟨C,hC,ho,hmeet⟩
  · obtain ⟨C,hC,ho⟩:=discHypercycleBranch_orthogonal axis hL hS
    exact ⟨C,hC,ho,hmeet⟩

theorem DiscGeodesicPencil.perpendicularBisector_iff (P : DiscGeodesicPencil) {a b : 𝔻} (hab : a≠b)
    {N : DiscLine} (hN : IsDiscPerpendicularBisector N a b) :
    N∈P.lines ↔ ∃S∈P.curves,a∈S ∧ b∈S := by
  rcases P with w | p | axis
  · exact discParabolicPencil_perpendicularBisector_iff w.property hab hN
  · exact discEllipticPencil_perpendicularBisector_iff p hab hN
  · exact discHyperbolicPencil_perpendicularBisector_iff axis hab hN

def DiscGeodesicPencil.GeneratedBy (P : DiscGeodesicPencil) (L M : DiscLine) : Prop :=
  L∈P.lines ∧ M∈P.lines ∧ L≠M

theorem DiscGeodesicPencil.GeneratedBy.ratioLine_iff {P : DiscGeodesicPencil} {L M : DiscLine}
    (h : P.GeneratedBy L M) (N : DiscLine) : N∈P.lines ↔ L.IsDistanceRatioLine M N := by
  obtain ⟨hL,hM,hne⟩:=h
  rcases P with w | p | axis
  · exact (L.parallel_isDistanceRatioLine_iff M (discParabolicPencil_members_parallel hL hM hne) w.val hL hM N).symm
  · exact (L.intersecting_isDistanceRatioLine_iff M (discEllipticPencil_members_intersecting p hL hM hne) p hL hM
    N).symm
  · exact (L.disjoint_isDistanceRatioLine_iff M (discHyperbolicPencil_members_hDisjoint axis hL hM hne) axis hL hM
    N).symm

def HGeodesicPencil.toDisc : HGeodesicPencil → DiscGeodesicPencil
  | .inl w => _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscGeodesicPencil.parabolic (extendedCayley
    w.val) ((idealBoundary_cayley_iff w.val).mp w.property)
  | .inr (.inl p) => _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscGeodesicPencil.elliptic (halfPlaneToDisc p)
  | .inr (.inr axis) => _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscGeodesicPencil.hyperbolic axis.toDiscLine

def DiscGeodesicPencil.toHalfPlane : DiscGeodesicPencil → HGeodesicPencil
  | .inl w => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.parabolic (extendedCayley.symm w.val)
      ((idealBoundary_cayley_iff (extendedCayley.symm w.val)).mpr (by simpa only [extendedCayley.apply_symm_apply] using w.property))
  | .inr (.inl p) => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.elliptic (discToHalfPlane p)
  | .inr (.inr axis) => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.hyperbolic axis.toHalfPlane

theorem HGeodesicPencil.mem_lines_cayley (P : HGeodesicPencil) (L : DiscLine) :
    L∈P.toDisc.lines ↔ L.toHalfPlane∈P.lines := by
  rcases P with w | p | axis
  · change _∈discParabolicPencil (extendedCayley w.val) ↔ _∈hParabolicPencil w.val
    rw [mem_discParabolicPencil_iff_halfPlane,extendedCayley.symm_apply_apply]
  · change halfPlaneToDisc p∈L.carrier ↔ p∈L.toHalfPlane.carrier
    rw [L.mem_carrier,discToHalfPlane_halfPlaneToDisc]
  · change _∈discHyperbolicPencil axis.toDiscLine ↔ _∈hHyperbolicPencil axis
    rw [mem_discHyperbolicPencil_iff_halfPlane,axis.toDiscLine_toHalfPlane]

theorem DiscGeodesicPencil.mem_lines_halfPlane (P : DiscGeodesicPencil) (L : DiscLine) :
    L∈P.lines ↔ L.toHalfPlane∈P.toHalfPlane.lines := by
  rcases P with w | p | axis
  · exact mem_discParabolicPencil_iff_halfPlane w.val L
  · exact L.mem_carrier p
  · exact mem_discHyperbolicPencil_iff_halfPlane axis L

theorem HGeodesicPencil.toDisc_toHalfPlane (P : HGeodesicPencil) : P.toDisc.toHalfPlane=P := by
  rcases P with w | p | axis
  · simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.toDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscGeodesicPencil.toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.parabolic,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscGeodesicPencil.parabolic]
  · change Sum.inr (Sum.inl (discToHalfPlane (halfPlaneToDisc p)))=_
    rw [discToHalfPlane_halfPlaneToDisc]
  · change Sum.inr (Sum.inr axis.toDiscLine.toHalfPlane)=_
    rw [axis.toDiscLine_toHalfPlane]

theorem DiscGeodesicPencil.toHalfPlane_toDisc (P : DiscGeodesicPencil) : P.toHalfPlane.toDisc=P := by
  rcases P with w | p | axis
  · simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscGeodesicPencil.toHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.toDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscGeodesicPencil.parabolic,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HGeodesicPencil.parabolic]
  · change Sum.inr (Sum.inl (halfPlaneToDisc (discToHalfPlane p)))=_
    rw [halfPlaneToDisc_discToHalfPlane]
  · change Sum.inr (Sum.inr axis.toHalfPlane.toDiscLine)=_
    rw [axis.toHalfPlane_spec]

theorem DiscGeodesicPencil.exists_generators (P : DiscGeodesicPencil) :
    ∃L M : DiscLine,P.GeneratedBy L M := by
  obtain ⟨L,M,hL,hM,hne⟩:=P.toHalfPlane.exists_generators
  refine ⟨L.toDiscLine,M.toDiscLine,?_,?_,?_⟩
  · rw [P.mem_lines_halfPlane,L.toDiscLine_toHalfPlane]
    exact hL
  · rw [P.mem_lines_halfPlane,M.toDiscLine_toHalfPlane]
    exact hM
  · intro he
    have hh:=congrArg DiscLine.toHalfPlane he
    rw [L.toDiscLine_toHalfPlane,M.toDiscLine_toHalfPlane] at hh
    exact hne hh

theorem exists_discGeodesicPencil_generatedBy (L M : DiscLine) (hne : L≠M) :
    ∃P : DiscGeodesicPencil,P.GeneratedBy L M := by
  obtain ⟨P,hL,hM,_⟩:=exists_hGeodesicPencil_generatedBy L.toHalfPlane M.toHalfPlane (DiscLine.toHalfPlane_injective.ne
    hne)
  exact ⟨P.toDisc,(P.mem_lines_cayley L).mpr hL,(P.mem_lines_cayley M).mpr hM,hne⟩

theorem DiscGeodesicPencil.GeneratedBy.classification {P : DiscGeodesicPencil} {L M : DiscLine}
    (h : P.GeneratedBy L M) :
    (∃w hw,P=_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscGeodesicPencil.parabolic w hw ∧ L.Parallel M) ∨
    (∃p,P=_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscGeodesicPencil.elliptic p ∧ L.Intersecting M) ∨
    (∃axis,P=_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscGeodesicPencil.hyperbolic axis ∧ L.HDisjoint M) := by
  obtain ⟨hL,hM,hne⟩:=h
  rcases P with w | p | axis
  · exact Or.inl ⟨w.val,w.property,rfl,discParabolicPencil_members_parallel hL hM hne⟩
  · exact Or.inr (Or.inl ⟨p,rfl,discEllipticPencil_members_intersecting p hL hM hne⟩)
  · exact Or.inr (Or.inr ⟨axis,rfl,discHyperbolicPencil_members_hDisjoint axis hL hM hne⟩)

/-- The actual generating pair determines the actual entire pencil of geodesics uniquely. -/
theorem HGeodesicPencil.GeneratedBy.lines_eq {P Q : HGeodesicPencil} {L M : HalfPlaneLine}
    (hP : P.GeneratedBy L M) (hQ : Q.GeneratedBy L M) : P.lines=Q.lines := by
  ext N
  exact (hP.ratioLine_iff N).trans (hQ.ratioLine_iff N).symm

theorem DiscGeodesicPencil.GeneratedBy.lines_eq {P Q : DiscGeodesicPencil} {L M : DiscLine}
    (hP : P.GeneratedBy L M) (hQ : Q.GeneratedBy L M) : P.lines=Q.lines := by
  ext N
  exact (hP.ratioLine_iff N).trans (hQ.ratioLine_iff N).symm

/-- Every actual generating pair determines a unique actual set of pencil geodesics. -/
theorem existsUnique_hGeodesicPencil_lines (L M : HalfPlaneLine) (hne : L≠M) :
    ∃!s : Set HalfPlaneLine,∃P : HGeodesicPencil,P.GeneratedBy L M ∧ s=P.lines := by
  obtain ⟨P,hP⟩:=exists_hGeodesicPencil_generatedBy L M hne
  refine ⟨P.lines,⟨P,hP,rfl⟩,?_⟩
  rintro s ⟨Q,hQ,rfl⟩
  exact hQ.lines_eq hP

theorem existsUnique_discGeodesicPencil_lines (L M : DiscLine) (hne : L≠M) :
    ∃!s : Set DiscLine,∃P : DiscGeodesicPencil,P.GeneratedBy L M ∧ s=P.lines := by
  obtain ⟨P,hP⟩:=exists_discGeodesicPencil_generatedBy L M hne
  refine ⟨P.lines,⟨P,hP,rfl⟩,?_⟩
  rintro s ⟨Q,hQ,rfl⟩
  exact hQ.lines_eq hP

/-- P7 holds for every actual pencil, with an explicitly existing actual generating pair. -/
theorem HGeodesicPencil.ratioLine_classification (P : HGeodesicPencil) :
    ∃L M : HalfPlaneLine,P.GeneratedBy L M ∧
      ∀N : HalfPlaneLine,N∈P.lines ↔ L.IsDistanceRatioLine M N := by
  obtain ⟨L,M,h⟩:=P.exists_generators
  exact ⟨L,M,h,h.ratioLine_iff⟩

theorem DiscGeodesicPencil.ratioLine_classification (P : DiscGeodesicPencil) :
    ∃L M : DiscLine,P.GeneratedBy L M ∧
      ∀N : DiscLine,N∈P.lines ↔ L.IsDistanceRatioLine M N := by
  obtain ⟨L,M,h⟩:=P.exists_generators
  exact ⟨L,M,h,h.ratioLine_iff⟩

/-- The single possible exceptional point is a genuine point, not an unbounded exceptional set. -/
theorem HGeodesicPencil.exceptional_subsingleton (P : HGeodesicPencil) :
    {z : ℍ | P.Exceptional z}.Subsingleton := by
  rcases P with w | p | axis
  · exact fun _ h=>h.elim
  · exact fun _ h _ k=>h.trans k.symm
  · exact fun _ h=>h.elim

theorem DiscGeodesicPencil.exceptional_subsingleton (P : DiscGeodesicPencil) :
    {z : 𝔻 | P.Exceptional z}.Subsingleton := by
  rcases P with w | p | axis
  · exact fun _ h=>h.elim
  · exact fun _ h _ k=>h.trans k.symm
  · exact fun _ h=>h.elim

/-- Genuine one-real-parameter descriptions, with the extra point allowing the vertical elliptic member. -/
theorem HGeodesicPencil.exists_parameterization (P : HGeodesicPencil) :
    ∃f : OnePoint ℝ → HalfPlaneLine,range f=P.lines := by
  rcases P with w | p | axis
  · obtain ⟨g,hg,he⟩:=exists_hParabolicChart w.val w.property
    let f : OnePoint ℝ → HalfPlaneLine:=fun x=>
      match x with
      | ∞ => (HalfPlaneLine.vertical 0).realGLMap g
      | (a : ℝ) => (HalfPlaneLine.vertical a).realGLMap g
    refine ⟨f,?_⟩
    ext L
    change L∈range f ↔ L∈hParabolicPencil w.val
    rw [←he,mem_hParabolicPencil_chart_iff g hg L]
    constructor
    · rintro ⟨x,rfl⟩
      cases x with
      | infty => exact ⟨0,rfl⟩
      | coe a => exact ⟨a,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨(a : OnePoint ℝ),rfl⟩
  · let f : OnePoint ℝ → HalfPlaneLine:=fun x=>
      match x with
      | ∞ => HalfPlaneLine.vertical p.re
      | (a : ℝ) => HalfPlaneLine.circle a ‖(p : ℂ)-(a : ℂ)‖ (norm_sub_real_pos a p)
    refine ⟨f,?_⟩
    ext L
    change L∈range f ↔ p∈L.carrier
    constructor
    · rintro ⟨x,rfl⟩
      cases x with
      | infty => rfl
      | coe a => rfl
    · intro hL
      cases L with
      | vertical a =>
        change p.re=a at hL
        refine ⟨∞,?_⟩
        change HalfPlaneLine.vertical p.re=HalfPlaneLine.vertical a
        rw [hL]
      | circle a r hr =>
        change ‖(p : ℂ)-(a : ℂ)‖=r at hL
        refine ⟨(a : OnePoint ℝ),?_⟩
        change HalfPlaneLine.circle a ‖(p : ℂ)-(a : ℂ)‖ _=HalfPlaneLine.circle a r hr
        congr 1
  · obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
    let f : OnePoint ℝ → HalfPlaneLine:=fun x=>
      match x with
      | ∞ => (HalfPlaneLine.circle 0 1 (by norm_num)).realGLMap g
      | (a : ℝ) => (HalfPlaneLine.circle 0 (Real.exp a) (Real.exp_pos a)).realGLMap g
    refine ⟨f,?_⟩
    ext L
    change L∈range f ↔ L∈hHyperbolicPencil ((HalfPlaneLine.vertical 0).realGLMap g)
    rw [mem_hHyperbolicPencil_chart_iff g L]
    constructor
    · rintro ⟨x,rfl⟩
      cases x with
      | infty => exact ⟨1,by norm_num,rfl⟩
      | coe a => exact ⟨Real.exp a,Real.exp_pos a,rfl⟩
    · rintro ⟨r,hr,rfl⟩
      refine ⟨(Real.log r : OnePoint ℝ),?_⟩
      change (HalfPlaneLine.circle 0 (Real.exp (Real.log r)) _).realGLMap g=_
      simp only [Real.exp_log hr]

theorem DiscGeodesicPencil.exists_parameterization (P : DiscGeodesicPencil) :
    ∃f : OnePoint ℝ → DiscLine,range f=P.lines := by
  obtain ⟨f,hf⟩:=P.toHalfPlane.exists_parameterization
  refine ⟨fun x=>(f x).toDiscLine,?_⟩
  ext L
  constructor
  · rintro ⟨x,rfl⟩
    rw [P.mem_lines_halfPlane,HalfPlaneLine.toDiscLine_toHalfPlane,←hf]
    exact mem_range_self x
  · intro hL
    have hm : L.toHalfPlane∈range f:=by rw [hf];exact (P.mem_lines_halfPlane L).mp hL
    obtain ⟨x,hx⟩:=hm
    exact ⟨x,by change (f x).toDiscLine=L; rw [hx,L.toHalfPlane_spec]⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
