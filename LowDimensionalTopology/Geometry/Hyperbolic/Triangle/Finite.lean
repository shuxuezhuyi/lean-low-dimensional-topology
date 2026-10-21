/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.AngleMeasures
public import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Actual vertex rays and triangle interiors
-/

@[expose] public section
open Set
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem HRayAt.eq_of_shared_point {z w : ℍ} (R S : HRayAt z)
    (hzw : z ≠ w) (hwR : w ∈ R.val) (hwS : w ∈ S.val) : R = S := by
  have hL : R.supportLine = S.supportLine :=
    R.supportLine.eq_of_two_points S.supportLine hzw R.start_mem_support
      (R.subset_support hwR) S.start_mem_support (S.subset_support hwS)
  obtain ⟨a,b,γ,s,_,_,hγ,hrange,hs,_,_,_,_⟩ :=
    R.supportLine.exists_rays_at z R.start_mem_support
  have hRI := R.isRay.eq_one_of_rays_at R.supportLine R.start_mem_support
    R.ideal_mem_support γ hγ.1 hrange s hs
  have hSI := S.isRay.eq_one_of_rays_at R.supportLine R.start_mem_support
    (hL.symm ▸ S.ideal_mem_support) γ hγ.1 hrange s hs
  apply Subtype.ext
  rcases hRI with hR | hR <;> rcases hSI with hS | hS
  · exact hR.trans hS.symm
  · exfalso
    have hw : w ∈ backwardHLineRay γ s ∩ forwardHLineRay γ s :=
      ⟨hS ▸ hwS,hR ▸ hwR⟩
    rw [hLineRay_inter hγ.1,hs] at hw
    exact hzw (mem_singleton_iff.mp hw).symm
  · exfalso
    have hw : w ∈ backwardHLineRay γ s ∩ forwardHLineRay γ s :=
      ⟨hR ▸ hwR,hS ▸ hwS⟩
    rw [hLineRay_inter hγ.1,hs] at hw
    exact hzw (mem_singleton_iff.mp hw).symm
  · exact hR.trans hS.symm

theorem existsUnique_hRayAt_through (z w : ℍ) (hzw : z ≠ w) :
    ∃! R : HRayAt z, w ∈ R.val := by
  obtain ⟨L,hz,hw⟩ := exists_halfPlaneLine_through z w hzw
  obtain ⟨a,b,_,he,hu,_⟩ := L.exists_canonical_rays_at z hz
  have ha : a ∈ halfPlaneIdealBoundary := (show a ∈ L.idealEndpoints from he.symm ▸ mem_insert a {b}).2
  have hb : b ∈ halfPlaneIdealBoundary := (show b ∈ L.idealEndpoints from he.symm ▸ mem_insert_of_mem a (mem_singleton
    b)).2
  have hw' : w ∈ hRay z a ∪ hRay z b := hu.symm ▸ hw
  rcases hw' with hw' | hw'
  · exact ⟨HRayAt.canonical z a ha,hw',fun S hS =>
      S.eq_of_shared_point (HRayAt.canonical z a ha) hzw hS hw'⟩
  · exact ⟨HRayAt.canonical z b hb,hw',fun S hS =>
      S.eq_of_shared_point (HRayAt.canonical z b hb) hzw hS hw'⟩

/-- The actual ray beginning at the first finite point and passing through the second. -/
def hRayThrough (z w : ℍ) (hzw : z ≠ w) : HRayAt z :=
  (existsUnique_hRayAt_through z w hzw).exists.choose

theorem hRayThrough_mem (z w : ℍ) (hzw : z ≠ w) : w ∈ (hRayThrough z w hzw).val :=
  (existsUnique_hRayAt_through z w hzw).exists.choose_spec

theorem hRayThrough_eq {z w : ℍ} (hzw : z ≠ w) (R : HRayAt z) (hw : w ∈ R.val) :
    hRayThrough z w hzw = R :=
  (hRayThrough z w hzw).eq_of_shared_point R hzw (hRayThrough_mem z w hzw) hw


/-- An actual h-line through two points, including a repeated point. -/
theorem exists_halfPlaneLine_through_any (z w : ℍ) :
    ∃ L : HalfPlaneLine, z ∈ L.carrier ∧ w ∈ L.carrier := by
  by_cases he : z = w
  · subst w
    exact ⟨.vertical z.re,rfl,rfl⟩
  · exact exists_halfPlaneLine_through z w he

/-- Three actual interior vertices, excluded precisely when one h-line contains all three. -/
structure HTriangle where
  a : ℍ
  b : ℍ
  c : ℍ
  noncollinear : ¬ ∃ L : HalfPlaneLine, a ∈ L.carrier ∧ b ∈ L.carrier ∧ c ∈ L.carrier

theorem HTriangle.a_ne_b (T : HTriangle) : T.a ≠ T.b := by
  intro he
  obtain ⟨L,ha,hc⟩ := exists_halfPlaneLine_through_any T.a T.c
  exact T.noncollinear ⟨L,ha,he ▸ ha,hc⟩

theorem HTriangle.b_ne_c (T : HTriangle) : T.b ≠ T.c := by
  intro he
  obtain ⟨L,ha,hb⟩ := exists_halfPlaneLine_through_any T.a T.b
  exact T.noncollinear ⟨L,ha,hb,he ▸ hb⟩

theorem HTriangle.c_ne_a (T : HTriangle) : T.c ≠ T.a := by
  intro he
  obtain ⟨L,ha,hb⟩ := exists_halfPlaneLine_through_any T.a T.b
  exact T.noncollinear ⟨L,ha,hb,he.symm ▸ ha⟩

def HTriangle.rayAB (T : HTriangle) : HRayAt T.a := hRayThrough T.a T.b T.a_ne_b

def HTriangle.rayAC (T : HTriangle) : HRayAt T.a := hRayThrough T.a T.c T.c_ne_a.symm

def HTriangle.rayBA (T : HTriangle) : HRayAt T.b := hRayThrough T.b T.a T.a_ne_b.symm

def HTriangle.rayBC (T : HTriangle) : HRayAt T.b := hRayThrough T.b T.c T.b_ne_c

def HTriangle.rayCA (T : HTriangle) : HRayAt T.c := hRayThrough T.c T.a T.c_ne_a

def HTriangle.rayCB (T : HTriangle) : HRayAt T.c := hRayThrough T.c T.b T.b_ne_c.symm

theorem HTriangle.b_mem_rayAB (T : HTriangle) : T.b ∈ T.rayAB.val :=
  hRayThrough_mem _ _ _

theorem HTriangle.c_mem_rayAC (T : HTriangle) : T.c ∈ T.rayAC.val :=
  hRayThrough_mem _ _ _

theorem HTriangle.a_mem_rayBA (T : HTriangle) : T.a ∈ T.rayBA.val :=
  hRayThrough_mem _ _ _

theorem HTriangle.c_mem_rayBC (T : HTriangle) : T.c ∈ T.rayBC.val :=
  hRayThrough_mem _ _ _

theorem HTriangle.a_mem_rayCA (T : HTriangle) : T.a ∈ T.rayCA.val :=
  hRayThrough_mem _ _ _

theorem HTriangle.b_mem_rayCB (T : HTriangle) : T.b ∈ T.rayCB.val :=
  hRayThrough_mem _ _ _

theorem HTriangle.proper_angleA (T : HTriangle) : T.rayAB.supportLine ≠ T.rayAC.supportLine := by
  intro he
  exact T.noncollinear ⟨T.rayAB.supportLine,T.rayAB.start_mem_support,
    T.rayAB.subset_support T.b_mem_rayAB,he.symm ▸ T.rayAC.subset_support T.c_mem_rayAC⟩

theorem HTriangle.proper_angleB (T : HTriangle) : T.rayBA.supportLine ≠ T.rayBC.supportLine := by
  intro he
  exact T.noncollinear ⟨T.rayBA.supportLine,T.rayBA.subset_support T.a_mem_rayBA,
    T.rayBA.start_mem_support,he.symm ▸ T.rayBC.subset_support T.c_mem_rayBC⟩

theorem HTriangle.proper_angleC (T : HTriangle) : T.rayCA.supportLine ≠ T.rayCB.supportLine := by
  intro he
  exact T.noncollinear ⟨T.rayCA.supportLine,T.rayCA.subset_support T.a_mem_rayCA,
    he.symm ▸ T.rayCB.subset_support T.b_mem_rayCB,T.rayCA.start_mem_support⟩

def HTriangle.angleA (T : HTriangle) : HAngle T.a := s(T.rayAB,T.rayAC)

def HTriangle.angleB (T : HTriangle) : HAngle T.b := s(T.rayBA,T.rayBC)

def HTriangle.angleC (T : HTriangle) : HAngle T.c := s(T.rayCA,T.rayCB)

def HTriangle.angleInteriorA (T : HTriangle) : Set ℍ := properHAngleInterior T.rayAB T.rayAC

def HTriangle.angleInteriorB (T : HTriangle) : Set ℍ := properHAngleInterior T.rayBA T.rayBC

def HTriangle.angleInteriorC (T : HTriangle) : Set ℍ := properHAngleInterior T.rayCA T.rayCB

/-- The actual source open triangle is the intersection of its three actual vertex-angle interiors. -/
def HTriangle.interior (T : HTriangle) : Set ℍ :=
  T.angleInteriorA ∩ T.angleInteriorB ∩ T.angleInteriorC

/-- The side opposite the first vertex is the genuine closed h-segment of the other vertices. -/
def HTriangle.sideA (T : HTriangle) : Set ℍ := closedHSegment T.b T.c

def HTriangle.sideB (T : HTriangle) : Set ℍ := closedHSegment T.c T.a

def HTriangle.sideC (T : HTriangle) : Set ℍ := closedHSegment T.a T.b

theorem HTriangle.interior_hConvex (T : HTriangle) : HConvex T.interior := by
  intro z hz w hw u hu
  exact ⟨⟨properHAngleInterior_hConvex _ _ T.proper_angleA z hz.1.1 w hw.1.1 hu,
    properHAngleInterior_hConvex _ _ T.proper_angleB z hz.1.2 w hw.1.2 hu⟩,
    properHAngleInterior_hConvex _ _ T.proper_angleC z hz.2 w hw.2 hu⟩

theorem HTriangle.interior_isOpen (T : HTriangle) : IsOpen T.interior :=
  ((properHAngleInterior_isOpen _ _ T.proper_angleA).inter
    (properHAngleInterior_isOpen _ _ T.proper_angleB)).inter
      (properHAngleInterior_isOpen _ _ T.proper_angleC)

theorem HTriangle.interior_isPreconnected (T : HTriangle) : IsPreconnected T.interior :=
  T.interior_hConvex.isPreconnected


def HTriangle.sideLineA (T : HTriangle) : HalfPlaneLine := T.rayBC.supportLine

def HTriangle.sideLineB (T : HTriangle) : HalfPlaneLine := T.rayCA.supportLine

def HTriangle.sideLineC (T : HTriangle) : HalfPlaneLine := T.rayAB.supportLine

theorem HTriangle.support_BA_eq (T : HTriangle) : T.rayBA.supportLine = T.sideLineC :=
  T.rayBA.supportLine.eq_of_two_points T.sideLineC T.a_ne_b
    (T.rayBA.subset_support T.a_mem_rayBA) T.rayBA.start_mem_support
    T.rayAB.start_mem_support (T.rayAB.subset_support T.b_mem_rayAB)

theorem HTriangle.support_AC_eq (T : HTriangle) : T.rayAC.supportLine = T.sideLineB :=
  T.rayAC.supportLine.eq_of_two_points T.sideLineB T.c_ne_a.symm
    T.rayAC.start_mem_support (T.rayAC.subset_support T.c_mem_rayAC)
    (T.rayCA.subset_support T.a_mem_rayCA) T.rayCA.start_mem_support

theorem HTriangle.support_CB_eq (T : HTriangle) : T.rayCB.supportLine = T.sideLineA :=
  T.rayCB.supportLine.eq_of_two_points T.sideLineA T.b_ne_c
    (T.rayCB.subset_support T.b_mem_rayCB) T.rayCB.start_mem_support
    T.rayBC.start_mem_support (T.rayBC.subset_support T.c_mem_rayBC)

theorem HTriangle.a_not_mem_sideLineA (T : HTriangle) : T.a ∉ T.sideLineA.carrier := by
  intro ha
  exact T.noncollinear ⟨T.sideLineA,ha,T.rayBC.start_mem_support,
    T.rayBC.subset_support T.c_mem_rayBC⟩

theorem HTriangle.b_not_mem_sideLineB (T : HTriangle) : T.b ∉ T.sideLineB.carrier := by
  intro hb
  exact T.noncollinear ⟨T.sideLineB,T.rayCA.subset_support T.a_mem_rayCA,
    hb,T.rayCA.start_mem_support⟩

theorem HTriangle.c_not_mem_sideLineC (T : HTriangle) : T.c ∉ T.sideLineC.carrier := by
  intro hc
  exact T.noncollinear ⟨T.sideLineC,T.rayAB.start_mem_support,
    T.rayAB.subset_support T.b_mem_rayAB,hc⟩

/-- The genuine component of the side complement containing the opposite actual vertex. -/
def HTriangle.halfPlaneA (T : HTriangle) : Set ℍ := openHHalfPlane T.sideLineA T.a

def HTriangle.halfPlaneB (T : HTriangle) : Set ℍ := openHHalfPlane T.sideLineB T.b

def HTriangle.halfPlaneC (T : HTriangle) : Set ℍ := openHHalfPlane T.sideLineC T.c

theorem HTriangle.angleInteriorA_eq_halfPlanes (T : HTriangle) :
    T.angleInteriorA = T.halfPlaneB ∩ T.halfPlaneC := by
  have h1 := hAngleSide_eq_component T.rayAB T.rayAC T.proper_angleA
    (show T.c ∈ T.rayAC.val \ {T.a} from ⟨T.c_mem_rayAC,T.c_ne_a⟩)
  have h2 := hAngleSide_eq_component T.rayAC T.rayAB (Ne.symm T.proper_angleA)
    (show T.b ∈ T.rayAB.val \ {T.a} from ⟨T.b_mem_rayAB,T.a_ne_b.symm⟩)
  change hAngleSide T.rayAB T.rayAC ∩ hAngleSide T.rayAC T.rayAB = _
  rw [h1,h2,T.support_AC_eq]
  exact inter_comm _ _

theorem HTriangle.angleInteriorB_eq_halfPlanes (T : HTriangle) :
    T.angleInteriorB = T.halfPlaneA ∩ T.halfPlaneC := by
  have h1 := hAngleSide_eq_component T.rayBA T.rayBC T.proper_angleB
    (show T.c ∈ T.rayBC.val \ {T.b} from ⟨T.c_mem_rayBC,T.b_ne_c.symm⟩)
  have h2 := hAngleSide_eq_component T.rayBC T.rayBA (Ne.symm T.proper_angleB)
    (show T.a ∈ T.rayBA.val \ {T.b} from ⟨T.a_mem_rayBA,T.a_ne_b⟩)
  change hAngleSide T.rayBA T.rayBC ∩ hAngleSide T.rayBC T.rayBA = _
  rw [h1,h2,T.support_BA_eq]
  exact inter_comm _ _

theorem HTriangle.angleInteriorC_eq_halfPlanes (T : HTriangle) :
    T.angleInteriorC = T.halfPlaneA ∩ T.halfPlaneB := by
  have h1 := hAngleSide_eq_component T.rayCA T.rayCB T.proper_angleC
    (show T.b ∈ T.rayCB.val \ {T.c} from ⟨T.b_mem_rayCB,T.b_ne_c⟩)
  have h2 := hAngleSide_eq_component T.rayCB T.rayCA (Ne.symm T.proper_angleC)
    (show T.a ∈ T.rayCA.val \ {T.c} from ⟨T.a_mem_rayCA,T.c_ne_a.symm⟩)
  change hAngleSide T.rayCA T.rayCB ∩ hAngleSide T.rayCB T.rayCA = _
  rw [h1,h2,T.support_CB_eq]
  exact inter_comm _ _

theorem HTriangle.interior_eq_halfPlanes (T : HTriangle) :
    T.interior = T.halfPlaneA ∩ T.halfPlaneB ∩ T.halfPlaneC := by
  rw [HTriangle.interior,T.angleInteriorA_eq_halfPlanes,T.angleInteriorB_eq_halfPlanes,
    T.angleInteriorC_eq_halfPlanes]
  ext x
  simp only [mem_inter_iff]
  tauto

theorem HTriangle.halfPlaneA_isOpen (T : HTriangle) : IsOpen T.halfPlaneA :=
  T.sideLineA.isClosed_carrier.isOpen_compl.connectedComponentIn

theorem HTriangle.halfPlaneB_isOpen (T : HTriangle) : IsOpen T.halfPlaneB :=
  T.sideLineB.isClosed_carrier.isOpen_compl.connectedComponentIn

theorem HTriangle.halfPlaneC_isOpen (T : HTriangle) : IsOpen T.halfPlaneC :=
  T.sideLineC.isClosed_carrier.isOpen_compl.connectedComponentIn

theorem HTriangle.a_mem_halfPlaneA (T : HTriangle) : T.a ∈ T.halfPlaneA :=
  mem_connectedComponentIn T.a_not_mem_sideLineA

theorem HTriangle.b_mem_halfPlaneB (T : HTriangle) : T.b ∈ T.halfPlaneB :=
  mem_connectedComponentIn T.b_not_mem_sideLineB

theorem HTriangle.c_mem_halfPlaneC (T : HTriangle) : T.c ∈ T.halfPlaneC :=
  mem_connectedComponentIn T.c_not_mem_sideLineC

theorem HTriangle.locally_angleA (T : HTriangle) : ∃ r > 0,
    Metric.ball T.a r ∩ T.interior = Metric.ball T.a r ∩ T.angleInteriorA := by
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp T.halfPlaneA_isOpen T.a T.a_mem_halfPlaneA
  refine ⟨r,hr,?_⟩
  rw [T.interior_eq_halfPlanes,T.angleInteriorA_eq_halfPlanes]
  ext x
  simp only [mem_inter_iff]
  constructor
  · tauto
  · rintro ⟨hx,hB,hC⟩
    exact ⟨hx,⟨hsub hx,hB⟩,hC⟩

theorem HTriangle.locally_angleB (T : HTriangle) : ∃ r > 0,
    Metric.ball T.b r ∩ T.interior = Metric.ball T.b r ∩ T.angleInteriorB := by
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp T.halfPlaneB_isOpen T.b T.b_mem_halfPlaneB
  refine ⟨r,hr,?_⟩
  rw [T.interior_eq_halfPlanes,T.angleInteriorB_eq_halfPlanes]
  ext x
  simp only [mem_inter_iff]
  constructor
  · tauto
  · rintro ⟨hx,hA,hC⟩
    exact ⟨hx,⟨hA,hsub hx⟩,hC⟩

theorem HTriangle.locally_angleC (T : HTriangle) : ∃ r > 0,
    Metric.ball T.c r ∩ T.interior = Metric.ball T.c r ∩ T.angleInteriorC := by
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp T.halfPlaneC_isOpen T.c T.c_mem_halfPlaneC
  refine ⟨r,hr,?_⟩
  rw [T.interior_eq_halfPlanes,T.angleInteriorC_eq_halfPlanes]
  ext x
  simp only [mem_inter_iff]
  constructor
  · tauto
  · rintro ⟨hx,hA,hB⟩
    exact ⟨hx,⟨hA,hB⟩,hsub hx⟩


theorem HTriangle.angleA_interior (T : HTriangle) : T.angleA.interior = some T.angleInteriorA :=
  hAngleInteriorPair_proper _ _ T.proper_angleA

theorem HTriangle.angleB_interior (T : HTriangle) : T.angleB.interior = some T.angleInteriorB :=
  hAngleInteriorPair_proper _ _ T.proper_angleB

theorem HTriangle.angleC_interior (T : HTriangle) : T.angleC.interior = some T.angleInteriorC :=
  hAngleInteriorPair_proper _ _ T.proper_angleC

/-- The unique actual native disc ray passing through two distinct finite points. -/
def discRayThrough (z w : 𝔻) (hzw : z ≠ w) : DiscRayAt z :=
  (hRayThrough (discToHalfPlane z) (discToHalfPlane w)
    (cayleyHomeomorph.symm.injective.ne hzw)).toDiscAt z

theorem discRayThrough_toHalfPlane (z w : 𝔻) (hzw : z ≠ w) :
    (discRayThrough z w hzw).toHalfPlane =
      hRayThrough (discToHalfPlane z) (discToHalfPlane w)
        (cayleyHomeomorph.symm.injective.ne hzw) :=
  (discRayHalfPlaneEquiv z).right_inv _

theorem discRayThrough_mem (z w : 𝔻) (hzw : z ≠ w) : w ∈ (discRayThrough z w hzw).val :=
  ⟨discToHalfPlane w,hRayThrough_mem _ _ _,halfPlaneToDisc_discToHalfPlane w⟩

theorem DiscRayAt.eq_of_shared_point {z w : 𝔻} (R S : DiscRayAt z)
    (hzw : z ≠ w) (hwR : w ∈ R.val) (hwS : w ∈ S.val) : R = S := by
  apply (discRayHalfPlaneEquiv z).injective
  exact R.toHalfPlane.eq_of_shared_point S.toHalfPlane
    (cayleyHomeomorph.symm.injective.ne hzw) ⟨w,hwR,rfl⟩ ⟨w,hwS,rfl⟩

theorem discRayThrough_eq {z w : 𝔻} (hzw : z ≠ w) (R : DiscRayAt z) (hw : w ∈ R.val) :
    discRayThrough z w hzw = R :=
  (discRayThrough z w hzw).eq_of_shared_point R hzw (discRayThrough_mem z w hzw) hw

/-- Actual native disc vertices with the actual noncollinearity condition. -/
structure DiscTriangle where
  a : 𝔻
  b : 𝔻
  c : 𝔻
  noncollinear : ¬ ∃ L : DiscLine, a ∈ L.carrier ∧ b ∈ L.carrier ∧ c ∈ L.carrier

def DiscTriangle.toHalfPlane (T : DiscTriangle) : HTriangle where
  a := discToHalfPlane T.a
  b := discToHalfPlane T.b
  c := discToHalfPlane T.c
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    apply T.noncollinear
    refine ⟨L.toDiscLine,?_,?_,?_⟩
    all_goals rw [L.toDiscLine_carrier,L.discCarrier_eq_cayley_image]
    · exact ⟨discToHalfPlane T.a,ha,halfPlaneToDisc_discToHalfPlane T.a⟩
    · exact ⟨discToHalfPlane T.b,hb,halfPlaneToDisc_discToHalfPlane T.b⟩
    · exact ⟨discToHalfPlane T.c,hc,halfPlaneToDisc_discToHalfPlane T.c⟩

theorem DiscTriangle.a_ne_b (T : DiscTriangle) : T.a ≠ T.b := by
  intro he
  exact T.toHalfPlane.a_ne_b (congrArg discToHalfPlane he)

theorem DiscTriangle.b_ne_c (T : DiscTriangle) : T.b ≠ T.c := by
  intro he
  exact T.toHalfPlane.b_ne_c (congrArg discToHalfPlane he)

theorem DiscTriangle.c_ne_a (T : DiscTriangle) : T.c ≠ T.a := by
  intro he
  exact T.toHalfPlane.c_ne_a (congrArg discToHalfPlane he)

def DiscTriangle.rayAB (T : DiscTriangle) : DiscRayAt T.a := discRayThrough T.a T.b T.a_ne_b

def DiscTriangle.rayAC (T : DiscTriangle) : DiscRayAt T.a := discRayThrough T.a T.c T.c_ne_a.symm

def DiscTriangle.rayBA (T : DiscTriangle) : DiscRayAt T.b := discRayThrough T.b T.a T.a_ne_b.symm

def DiscTriangle.rayBC (T : DiscTriangle) : DiscRayAt T.b := discRayThrough T.b T.c T.b_ne_c

def DiscTriangle.rayCA (T : DiscTriangle) : DiscRayAt T.c := discRayThrough T.c T.a T.c_ne_a

def DiscTriangle.rayCB (T : DiscTriangle) : DiscRayAt T.c := discRayThrough T.c T.b T.b_ne_c.symm

def DiscTriangle.angleA (T : DiscTriangle) : DiscAngle T.a := s(T.rayAB,T.rayAC)

def DiscTriangle.angleB (T : DiscTriangle) : DiscAngle T.b := s(T.rayBA,T.rayBC)

def DiscTriangle.angleC (T : DiscTriangle) : DiscAngle T.c := s(T.rayCA,T.rayCB)

def DiscTriangle.angleInteriorA (T : DiscTriangle) : Set 𝔻 := properDiscAngleInterior T.rayAB T.rayAC

def DiscTriangle.angleInteriorB (T : DiscTriangle) : Set 𝔻 := properDiscAngleInterior T.rayBA T.rayBC

def DiscTriangle.angleInteriorC (T : DiscTriangle) : Set 𝔻 := properDiscAngleInterior T.rayCA T.rayCB

def DiscTriangle.interior (T : DiscTriangle) : Set 𝔻 :=
  T.angleInteriorA ∩ T.angleInteriorB ∩ T.angleInteriorC

def DiscTriangle.sideA (T : DiscTriangle) : Set 𝔻 := closedDiscHSegment T.b T.c

def DiscTriangle.sideB (T : DiscTriangle) : Set 𝔻 := closedDiscHSegment T.c T.a

def DiscTriangle.sideC (T : DiscTriangle) : Set 𝔻 := closedDiscHSegment T.a T.b

theorem DiscTriangle.angleInteriorA_eq_cayley (T : DiscTriangle) :
    T.angleInteriorA = halfPlaneToDisc '' T.toHalfPlane.angleInteriorA := by
  change halfPlaneToDisc '' properHAngleInterior
    (discRayThrough T.a T.b T.a_ne_b).toHalfPlane
    (discRayThrough T.a T.c T.c_ne_a.symm).toHalfPlane = _
  rw [discRayThrough_toHalfPlane,discRayThrough_toHalfPlane]
  rfl

theorem DiscTriangle.angleInteriorB_eq_cayley (T : DiscTriangle) :
    T.angleInteriorB = halfPlaneToDisc '' T.toHalfPlane.angleInteriorB := by
  change halfPlaneToDisc '' properHAngleInterior
    (discRayThrough T.b T.a T.a_ne_b.symm).toHalfPlane
    (discRayThrough T.b T.c T.b_ne_c).toHalfPlane = _
  rw [discRayThrough_toHalfPlane,discRayThrough_toHalfPlane]
  rfl

theorem DiscTriangle.angleInteriorC_eq_cayley (T : DiscTriangle) :
    T.angleInteriorC = halfPlaneToDisc '' T.toHalfPlane.angleInteriorC := by
  change halfPlaneToDisc '' properHAngleInterior
    (discRayThrough T.c T.a T.c_ne_a).toHalfPlane
    (discRayThrough T.c T.b T.b_ne_c.symm).toHalfPlane = _
  rw [discRayThrough_toHalfPlane,discRayThrough_toHalfPlane]
  rfl

theorem DiscTriangle.interior_eq_cayley (T : DiscTriangle) :
    T.interior = halfPlaneToDisc '' T.toHalfPlane.interior := by
  rw [DiscTriangle.interior,T.angleInteriorA_eq_cayley,T.angleInteriorB_eq_cayley,
    T.angleInteriorC_eq_cayley,HTriangle.interior]
  rw [image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective),
    image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective)]

theorem DiscTriangle.interior_discHConvex (T : DiscTriangle) : DiscHConvex T.interior := by
  rw [T.interior_eq_cayley]
  exact (hConvex_iff_cayley_discHConvex _).mp T.toHalfPlane.interior_hConvex

theorem DiscTriangle.interior_isOpen (T : DiscTriangle) : IsOpen T.interior := by
  rw [T.interior_eq_cayley]
  exact cayleyHomeomorph.isOpenMap _ T.toHalfPlane.interior_isOpen


theorem DiscTriangle.proper_angleA (T : DiscTriangle) : T.rayAB.supportLine ≠ T.rayAC.supportLine := by
  apply (T.rayAB.different_supports_iff T.rayAC).mpr
  change (discRayThrough T.a T.b T.a_ne_b).toHalfPlane.supportLine ≠
    (discRayThrough T.a T.c T.c_ne_a.symm).toHalfPlane.supportLine
  rw [discRayThrough_toHalfPlane,discRayThrough_toHalfPlane]
  exact T.toHalfPlane.proper_angleA

theorem DiscTriangle.proper_angleB (T : DiscTriangle) : T.rayBA.supportLine ≠ T.rayBC.supportLine := by
  apply (T.rayBA.different_supports_iff T.rayBC).mpr
  change (discRayThrough T.b T.a T.a_ne_b.symm).toHalfPlane.supportLine ≠
    (discRayThrough T.b T.c T.b_ne_c).toHalfPlane.supportLine
  rw [discRayThrough_toHalfPlane,discRayThrough_toHalfPlane]
  exact T.toHalfPlane.proper_angleB

theorem DiscTriangle.proper_angleC (T : DiscTriangle) : T.rayCA.supportLine ≠ T.rayCB.supportLine := by
  apply (T.rayCA.different_supports_iff T.rayCB).mpr
  change (discRayThrough T.c T.a T.c_ne_a).toHalfPlane.supportLine ≠
    (discRayThrough T.c T.b T.b_ne_c.symm).toHalfPlane.supportLine
  rw [discRayThrough_toHalfPlane,discRayThrough_toHalfPlane]
  exact T.toHalfPlane.proper_angleC

theorem DiscTriangle.angleA_interior (T : DiscTriangle) : T.angleA.interior = some T.angleInteriorA :=
  discAngleInteriorPair_proper _ _ T.proper_angleA

theorem DiscTriangle.angleB_interior (T : DiscTriangle) : T.angleB.interior = some T.angleInteriorB :=
  discAngleInteriorPair_proper _ _ T.proper_angleB

theorem DiscTriangle.angleC_interior (T : DiscTriangle) : T.angleC.interior = some T.angleInteriorC :=
  discAngleInteriorPair_proper _ _ T.proper_angleC

/-- A ball for the genuine weighted-path disc metric is the actual Cayley image of an H ball. -/
theorem cayley_image_ball_at_disc (q : 𝔻) (r : ℝ) :
    letI := discHyperbolicMetric
    halfPlaneToDisc '' Metric.ball (discToHalfPlane q) r = Metric.ball q r := by
  let := discHyperbolicMetric
  ext w
  constructor
  · rintro ⟨x,hx,rfl⟩
    change dist (discToHalfPlane (halfPlaneToDisc x)) (discToHalfPlane q) < r
    rw [discToHalfPlane_halfPlaneToDisc]
    exact hx
  · intro hw
    exact ⟨discToHalfPlane w,hw,halfPlaneToDisc_discToHalfPlane w⟩

theorem DiscTriangle.locally_angleA (T : DiscTriangle) :
    letI := discHyperbolicMetric
    ∃ r > 0, Metric.ball T.a r ∩ T.interior = Metric.ball T.a r ∩ T.angleInteriorA := by
  let := discHyperbolicMetric
  obtain ⟨r,hr,he⟩ := T.toHalfPlane.locally_angleA
  refine ⟨r,hr,?_⟩
  have him := congrArg (fun U : Set ℍ => halfPlaneToDisc '' U) he
  rw [image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective),
    image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective)] at him
  change halfPlaneToDisc '' Metric.ball (discToHalfPlane T.a) r ∩
    halfPlaneToDisc '' T.toHalfPlane.interior =
    halfPlaneToDisc '' Metric.ball (discToHalfPlane T.a) r ∩
    halfPlaneToDisc '' T.toHalfPlane.angleInteriorA at him
  rw [cayley_image_ball_at_disc,← T.interior_eq_cayley,← T.angleInteriorA_eq_cayley] at him
  exact him

theorem DiscTriangle.locally_angleB (T : DiscTriangle) :
    letI := discHyperbolicMetric
    ∃ r > 0, Metric.ball T.b r ∩ T.interior = Metric.ball T.b r ∩ T.angleInteriorB := by
  let := discHyperbolicMetric
  obtain ⟨r,hr,he⟩ := T.toHalfPlane.locally_angleB
  refine ⟨r,hr,?_⟩
  have him := congrArg (fun U : Set ℍ => halfPlaneToDisc '' U) he
  rw [image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective),
    image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective)] at him
  change halfPlaneToDisc '' Metric.ball (discToHalfPlane T.b) r ∩
    halfPlaneToDisc '' T.toHalfPlane.interior =
    halfPlaneToDisc '' Metric.ball (discToHalfPlane T.b) r ∩
    halfPlaneToDisc '' T.toHalfPlane.angleInteriorB at him
  rw [cayley_image_ball_at_disc,← T.interior_eq_cayley,← T.angleInteriorB_eq_cayley] at him
  exact him

theorem DiscTriangle.locally_angleC (T : DiscTriangle) :
    letI := discHyperbolicMetric
    ∃ r > 0, Metric.ball T.c r ∩ T.interior = Metric.ball T.c r ∩ T.angleInteriorC := by
  let := discHyperbolicMetric
  obtain ⟨r,hr,he⟩ := T.toHalfPlane.locally_angleC
  refine ⟨r,hr,?_⟩
  have him := congrArg (fun U : Set ℍ => halfPlaneToDisc '' U) he
  rw [image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective),
    image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective)] at him
  change halfPlaneToDisc '' Metric.ball (discToHalfPlane T.c) r ∩
    halfPlaneToDisc '' T.toHalfPlane.interior =
    halfPlaneToDisc '' Metric.ball (discToHalfPlane T.c) r ∩
    halfPlaneToDisc '' T.toHalfPlane.angleInteriorC at him
  rw [cayley_image_ball_at_disc,← T.interior_eq_cayley,← T.angleInteriorC_eq_cayley] at him
  exact him

end
end LowDimensionalTopology.Geometry.Hyperbolic
