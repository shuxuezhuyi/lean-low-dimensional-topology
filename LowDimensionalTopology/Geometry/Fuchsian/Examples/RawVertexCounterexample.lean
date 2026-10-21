module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareVertexCycles
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativePoincarePolygons
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareSideCompatibility
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeLineReflections
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HalfPlaneLorentzReflections
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicHalfTurns
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeCompactifiedSideGeometry
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Quotient.PolygonJordanModel
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare
public import Mathlib.Analysis.Convex.GaugeRescale
@[expose] public section
noncomputable section
open Set Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian.RawVertexCounterexample
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

def axisMirror : ℍ ≃ᵢ ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (.vertical
  0)
def circleMirror : ℍ ≃ᵢ ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (.circle 0 2 (by norm_num))
def halfTurn : ℍ ≃ᵢ ℍ := axisMirror * circleMirror

theorem axisMirror_re (z : ℍ) : (axisMirror z).re = -z.re := by
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_re 0 z).trans (by ring)

theorem axisMirror_im (z : ℍ) : (axisMirror
  z).im = z.im := _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_im 0 z

theorem circleMirror_re (z : ℍ) : (circleMirror z).re = 4*z.re/(z.re^2+z.im^2) := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 2 _ z).re=_
  simpa only [
    sub_zero,zero_add,show (2:ℝ)^2=4 by norm_num] using
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_re 0 2 (by norm_num) z

theorem circleMirror_im (z : ℍ) : (circleMirror z).im = 4*z.im/(z.re^2+z.im^2) := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 2 _ z).im=_
  simpa only [
    sub_zero,show (2:ℝ)^2=4 by norm_num] using
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_im 0 2 (by norm_num) z

theorem axisMirror_involutive : Function.Involutive axisMirror :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).reflection_involutive

theorem circleMirror_involutive : Function.Involutive circleMirror :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 2 (by norm_num)).reflection_involutive

theorem axis_circle_commute : Commute axisMirror circleMirror := by
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change (axisMirror (circleMirror z)).re=(circleMirror (axisMirror z)).re
    rw [axisMirror_re,circleMirror_re,circleMirror_re,axisMirror_re,axisMirror_im]
    ring
  · change (axisMirror (circleMirror z)).im=(circleMirror (axisMirror z)).im
    rw [axisMirror_im,circleMirror_im,circleMirror_im,axisMirror_re,axisMirror_im]
    ring

theorem halfTurn_involutive : Function.Involutive halfTurn := by
  intro z
  have he:=congrArg (fun f : ℍ≃ᵢℍ=>f (circleMirror z)) axis_circle_commute.eq
  change axisMirror (circleMirror (axisMirror (circleMirror z)))=z
  change axisMirror (circleMirror (circleMirror z))=circleMirror (axisMirror (circleMirror z)) at he
  rw [←he,circleMirror_involutive,axisMirror_involutive]

theorem halfTurn_re (z : ℍ) : (halfTurn z).re = -(4*z.re/(z.re^2+z.im^2)) := by
  change (axisMirror (circleMirror z)).re=_
  rw [axisMirror_re,circleMirror_re]

theorem halfTurn_im (z : ℍ) : (halfTurn z).im = 4*z.im/(z.re^2+z.im^2) := by
  change (axisMirror (circleMirror z)).im=_
  rw [axisMirror_im,circleMirror_im]

def vertexA : ℍ := ⟨Complex.I,by norm_num⟩
def vertexB : ℍ := ⟨4*Complex.I,by norm_num⟩

theorem halfTurn_vertexA : halfTurn vertexA=vertexB := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change (halfTurn vertexA).re=vertexB.re
    rw [halfTurn_re]
    norm_num [vertexA,vertexB]
  · change (halfTurn vertexA).im=vertexB.im
    rw [halfTurn_im]
    norm_num [vertexA,vertexB]

theorem halfTurn_vertexB : halfTurn vertexB=vertexA := by
  rw [←halfTurn_vertexA]
  exact halfTurn_involutive vertexA

def sideSet (i : Fin 3) : Set ℍ :=
  ![{z | z.re=0 ∧ z.im≤1},{z | z.re=0 ∧ 1≤z.im ∧ z.im≤4},
    {z | z.re=0 ∧ 4≤z.im}] i

theorem sideSet_axis (i : Fin 3) {z : ℍ} (hz:z∈sideSet i) : z.re=0 := by
  fin_cases i <;> exact hz.1

theorem sideSet_nonempty (i : Fin 3) : (sideSet i).Nonempty := by
  fin_cases i
  · exact ⟨vertexA,by norm_num [sideSet,vertexA]⟩
  · exact ⟨vertexA,by norm_num [sideSet,vertexA]⟩
  · exact ⟨vertexB,by norm_num [sideSet,vertexB]⟩

theorem sides_union : (⋃ i,sideSet i)={z:ℍ|z.re=0} := by
  ext z
  simp only [mem_iUnion,mem_ofPred_eq]
  constructor
  · rintro ⟨i,hi⟩
    exact sideSet_axis i hi
  · intro hz
    by_cases h1:z.im≤1
    · exact ⟨0,hz,h1⟩
    · by_cases h4:z.im≤4
      · exact ⟨1,hz,(not_le.mp h1).le,h4⟩
      · exact ⟨2,hz,(not_le.mp h4).le⟩

def polygon : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ where
  interior := {z|0<z.re}
  interior_nonempty := ⟨⟨1+Complex.I,by norm_num⟩,by norm_num⟩
  sides := range sideSet
  sides_nonempty := ⟨sideSet 0,mem_range_self _⟩
  side_nonempty := by rintro s ⟨i,rfl⟩;exact sideSet_nonempty i
  disjoint := by
    apply disjoint_left.mpr
    rintro z hz ⟨s,⟨i,rfl⟩,hi⟩
    exact (ne_of_gt hz) (sideSet_axis i hi)

theorem polygon_boundary : polygon.boundary={z:ℍ|z.re=0} := by
  change ⋃₀ range sideSet=_
  rw [sUnion_range,sides_union]

theorem polygon_carrier : polygon.carrier={z:ℍ|0≤z.re} := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon.carrier,polygon_boundary]
  ext z
  change 0<z.re ∨z.re=0 ↔0≤z.re
  constructor
  · rintro (h|h)
    · exact h.le
    · exact h.ge
  · intro h
    rcases lt_or_eq_of_le h with h|h
    · exact Or.inl h
    · exact Or.inr h.symm

theorem middle_preserved (z : ℍ) (hz:z∈sideSet 1) : halfTurn z∈sideSet 1 := by
  rcases hz with ⟨hre,hlo,hhi⟩
  change (halfTurn z).re=0 ∧1≤(halfTurn z).im ∧(halfTurn z).im≤4
  have hpos : 0<z.im^2:=sq_pos_of_pos z.im_pos
  refine ⟨?_,?_,?_⟩
  · rw [halfTurn_re,hre]
    norm_num
  · rw [halfTurn_im,hre]
    norm_num only [zero_pow,zero_add]
    apply (le_div_iff₀ hpos).mpr
    nlinarith
  · rw [halfTurn_im,hre]
    norm_num only [zero_pow,zero_add]
    apply (div_le_iff₀ hpos).mpr
    nlinarith

theorem axisMirror_fixed {z : ℍ} (hz:z.re=0) : axisMirror z=z := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change (axisMirror z).re=z.re
    rw [axisMirror_re,hz,neg_zero]
  · exact axisMirror_im z

theorem axisMirror_side_image (i : Fin 3) : axisMirror '' sideSet i=sideSet i := by
  apply subset_antisymm
  · rintro _ ⟨z,hz,rfl⟩
    rwa [axisMirror_fixed (sideSet_axis i hz)]
  · intro z hz
    exact ⟨z,hz,axisMirror_fixed (sideSet_axis i hz)⟩

theorem halfTurn_middle_image : halfTurn '' sideSet 1=sideSet 1 := by
  apply subset_antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact middle_preserved z hz
  · intro z hz
    exact ⟨halfTurn z,middle_preserved z hz,halfTurn_involutive z⟩

theorem axisMirror_sq : axisMirror*axisMirror=1 := by
  apply IsometryEquiv.ext
  exact axisMirror_involutive

theorem halfTurn_sq : halfTurn*halfTurn=1 := by
  apply IsometryEquiv.ext
  exact halfTurn_involutive

def middleSide : polygon.Side := ⟨sideSet 1,mem_range_self _⟩

local instance counterexampleSideDecEq : DecidableEq polygon.Side := Classical.decEq _

def pairing : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) polygon where
  paired:=Equiv.refl _
  involutive:=fun _=>rfl
  element s:=if s=middleSide then halfTurn else axisMirror
  element_paired:=by
    intro s
    change (if s=middleSide then halfTurn else axisMirror)=
      (if s=middleSide then halfTurn else axisMirror)⁻¹
    split
    · exact eq_inv_of_mul_eq_one_right halfTurn_sq
    · exact eq_inv_of_mul_eq_one_right axisMirror_sq
  side_image:=by
    intro s
    change (if s=middleSide then halfTurn else axisMirror) • s.val=s.val
    by_cases hs:s=middleSide
    · rw [ite_eq_left hs]
      subst s
      change halfTurn '' sideSet 1=sideSet 1
      exact halfTurn_middle_image
    · rw [ite_eq_right hs]
      change axisMirror '' s.val=s.val
      obtain ⟨i,hi⟩:=s.property
      rw [←hi]
      exact axisMirror_side_image i

theorem pairing_middle : pairing.element middleSide=halfTurn := by
  simp only [pairing,ite_true]

theorem halfTurn_re_nonneg_iff (z : ℍ) : 0≤(halfTurn z).re ↔z.re≤0 := by
  have hd:0<z.re^2+z.im^2:=by nlinarith [sq_nonneg z.re,sq_pos_of_pos z.im_pos]
  rw [halfTurn_re,neg_nonneg,div_le_iff₀ hd]
  constructor <;>intro h <;>nlinarith

theorem halfTurn_re_pos_iff (z : ℍ) : 0<(halfTurn z).re ↔z.re<0 := by
  have hd:0<z.re^2+z.im^2:=by nlinarith [sq_nonneg z.re,sq_pos_of_pos z.im_pos]
  rw [halfTurn_re,neg_pos,div_lt_iff₀ hd]
  constructor <;>intro h <;>nlinarith

theorem halfTurn_right_image : halfTurn '' polygon.interior={z:ℍ|z.re<0} := by
  apply subset_antisymm
  · rintro _ ⟨z,hz,rfl⟩
    have h:=halfTurn_re_pos_iff (halfTurn z)
    rw [halfTurn_involutive] at h
    exact h.mp hz
  · intro z hz
    exact ⟨halfTurn z,(halfTurn_re_pos_iff z).mpr hz,halfTurn_involutive z⟩

theorem circleMirror_right_image : circleMirror '' polygon.interior=polygon.interior := by
  have hp (z:ℍ):0<(circleMirror z).re ↔0<z.re:=by
    have hd:0<z.re^2+z.im^2:=by nlinarith [sq_nonneg z.re,sq_pos_of_pos z.im_pos]
    rw [circleMirror_re]
    constructor
    · intro h
      have hnum:=((div_pos_iff_of_pos_right hd).mp h)
      linarith
    · intro h
      exact div_pos (mul_pos (by norm_num) h) hd
  apply subset_antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact (hp z).mpr hz
  · intro z hz
    exact ⟨circleMirror z,(hp z).mpr hz,circleMirror_involutive z⟩

def pointA : polygon.Point := ⟨vertexA,by rw [polygon_carrier];norm_num [vertexA]⟩
def pointB : polygon.Point := ⟨vertexB,by rw [polygon_carrier];norm_num [vertexB]⟩
def markedVertices : Set polygon.Point := {pointA,pointB}
def middleGenerator : pairing.Generated := pairing.generator middleSide

theorem middleGenerator_apply (z:ℍ) : middleGenerator •z=halfTurn z := by
  change pairing.element middleSide z=halfTurn z
  rw [pairing_middle]

theorem middleGenerator_sq : middleGenerator*middleGenerator=1 := by
  apply Subtype.ext
  change pairing.element middleSide *pairing.element middleSide=1
  rw [pairing_middle,halfTurn_sq]

theorem markedVertex_on_middle {x:polygon.Point} (hx:x∈markedVertices) : x.val∈middleSide.val := by
  rcases hx with rfl|rfl <;>norm_num [middleSide,pointA,pointB,sideSet,vertexA,vertexB]

def twoPieceCycle (x y:polygon.Point) (hx:x∈markedVertices) (hy:y∈markedVertices)
    (hxy:halfTurn x.val=y.val) (hyx:halfTurn y.val=x.val) (r:ℝ) (hr:0<r) :
    pairing.VertexCycle markedVertices x r where
  radius_pos:=hr
  lengthPred:=1
  copies:=![(1,x),(middleGenerator,y)]
  base:=rfl
  vertices:=by intro i;fin_cases i;exact hx;exact hy
  adjacent:=by
    intro i
    fin_cases i
    refine ⟨middleSide,markedVertex_on_middle hx,?_,?_⟩
    · exact hxy.symm.trans (middleGenerator_apply x.val).symm
    · exact middleGenerator_sq.symm
  closing:=by
    refine ⟨middleSide,markedVertex_on_middle hy,?_,?_⟩
    · exact hyx.symm.trans (middleGenerator_apply y.val).symm
    · exact (one_mul middleGenerator).symm
  covers:=by
    ext z
    constructor
    · intro hz
      obtain ⟨i,w,hw,he⟩:=mem_iUnion.mp hz
      fin_cases i
      · change (1:pairing.Generated)•w=z at he
        simpa only [one_smul] using he ▸ hw.2
      · change middleGenerator •w=z at he
        rw [middleGenerator_apply] at he
        have hd:=halfTurn.isometry.dist_eq w y.val
        rw [hyx,he] at hd
        change dist z x.val<r
        exact hd.trans_lt hw.2
    · intro hz
      by_cases h:z.re≥0
      · refine mem_iUnion.mpr ⟨0,z,⟨?_,hz⟩,?_⟩
        · exact (congrArg (fun s:Set ℍ=>z∈s) polygon_carrier).mpr h
        · exact one_smul _ _
      · refine mem_iUnion.mpr ⟨1,halfTurn z,⟨?_,?_⟩,?_⟩
        · rw [polygon_carrier]
          exact (halfTurn_re_nonneg_iff z).mpr (not_le.mp h).le
        · have hd:=halfTurn.isometry.dist_eq z x.val
          rw [hxy] at hd
          change dist (halfTurn z) y.val<r
          exact hd.trans_lt hz
        · change middleGenerator •halfTurn z=z
          rw [middleGenerator_apply,halfTurn_involutive]
  nonoverlap:=by
    have hD:Disjoint (pairing.vertexCycleInteriorPiece (1,x) r)
        (pairing.vertexCycleInteriorPiece (middleGenerator,y) r):=by
      apply disjoint_left.mpr
      rintro z ⟨a,ha,he⟩ ⟨b,hb,hbe⟩
      change (1:pairing.Generated)•a=z at he
      change middleGenerator •b=z at hbe
      rw [one_smul] at he
      rw [middleGenerator_apply] at hbe
      have hn: z.re<0:=by
        rw [←hbe]
        rw [halfTurn_re]
        have hd:0<b.re^2+b.im^2:=by nlinarith [sq_nonneg b.re,sq_pos_of_pos b.im_pos]
        have hi:=div_pos (mul_pos (by norm_num : (0:ℝ)<4) (show 0<b.re from hb.1)) hd
        linarith
      have hp:0<z.re:=he ▸ ha.1
      linarith
    intro i j hij
    fin_cases i <;>fin_cases j
    · exact (hij rfl).elim
    · exact hD
    · exact hD.symm
    · exact (hij rfl).elim

theorem weak_vertex_condition : pairing.FiniteVertexCycleCondition markedVertices := by
  intro x hx
  rcases hx with rfl|rfl
  · exact ⟨1,⟨twoPieceCycle pointA pointB (by simp [markedVertices])
      (by simp [markedVertices]) halfTurn_vertexA halfTurn_vertexB 1 (by norm_num)⟩⟩
  · exact ⟨1,⟨twoPieceCycle pointB pointA (by simp [markedVertices])
      (by simp [markedVertices]) halfTurn_vertexB halfTurn_vertexA 1 (by norm_num)⟩⟩

theorem opposite_sides (s:polygon.Side) (z:ℍ) : pairing.OppositeSideNeighborhoods s z := by
  let : IsIsometricSMul pairing.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  apply (pairing.oppositeSideNeighborhoods_iff s z).mpr
  have he:polygon.carrier ∪(fun w:ℍ=>pairing.generator s•w)⁻¹'polygon.carrier=univ:=by
    apply eq_univ_of_forall
    intro w
    by_cases h:0≤w.re
    · exact Or.inl (polygon_carrier ▸ h)
    · right
      change pairing.element s w∈polygon.carrier
      rw [polygon_carrier]
      change 0≤((if s=middleSide then halfTurn else axisMirror) w).re
      split
      · exact (halfTurn_re_nonneg_iff w).mpr (not_le.mp h).le
      · rw [axisMirror_re]
        linarith [not_le.mp h]
  rw [he]
  exact Filter.univ_mem

def lowerSide : polygon.Side := ⟨sideSet 0,mem_range_self _⟩

theorem lowerSide_ne_middle : lowerSide≠middleSide := by
  intro h
  have he:=congrArg (fun s:polygon.Side=>vertexB∈s.val) h
  norm_num [lowerSide,middleSide,sideSet,vertexB] at he

theorem pairing_lower : pairing.element lowerSide=axisMirror := by
  change (if lowerSide=middleSide then halfTurn else axisMirror)=_
  exact ite_eq_right lowerSide_ne_middle

def lowerGenerator : pairing.Generated := pairing.generator lowerSide
def extraGenerator : pairing.Generated := lowerGenerator*middleGenerator

theorem lowerGenerator_apply (z:ℍ) : lowerGenerator•z=axisMirror z := by
  change pairing.element lowerSide z=axisMirror z
  rw [pairing_lower]

theorem lowerGenerator_sq : lowerGenerator*lowerGenerator=1 := by
  apply Subtype.ext
  change pairing.element lowerSide*pairing.element lowerSide=1
  rw [pairing_lower,axisMirror_sq]

theorem extraGenerator_apply (z:ℍ) : extraGenerator•z=circleMirror z := by
  change (lowerGenerator*middleGenerator)•z=_
  rw [mul_smul,lowerGenerator_apply,middleGenerator_apply]
  change axisMirror (axisMirror (circleMirror z))=circleMirror z
  exact axisMirror_involutive _

theorem circleMirror_vertexA : circleMirror vertexA=vertexB := by
  have h:=congrArg axisMirror halfTurn_vertexA
  change axisMirror (axisMirror (circleMirror vertexA))=axisMirror vertexB at h
  rw [axisMirror_involutive,axisMirror_fixed (by norm_num [vertexB])] at h
  exact h

theorem circleMirror_vertexB : circleMirror vertexB=vertexA := by
  rw [←circleMirror_vertexA]
  exact circleMirror_involutive vertexA

theorem extraGenerator_ne_one : extraGenerator≠1 := by
  intro h
  have he:=congrArg (fun g:pairing.Generated=>g•vertexA) h
  rw [extraGenerator_apply,circleMirror_vertexA,one_smul] at he
  have hi:=congrArg UpperHalfPlane.im he
  norm_num [vertexA,vertexB] at hi

theorem extra_center_glued : pairing.project (extraGenerator,pointB)=pairing.project (1,pointA) := by
  have h1:pairing.Step (1,pointA) (lowerGenerator,pointA):=by
    refine Or.inr ⟨lowerSide,?_,?_,?_⟩
    · norm_num [lowerSide,sideSet,pointA,vertexA]
    · change vertexA=lowerGenerator•vertexA
      rw [lowerGenerator_apply]
      exact (axisMirror_fixed (by norm_num [pointA,vertexA])).symm
    · exact lowerGenerator_sq.symm
  have h2:pairing.Step (lowerGenerator,pointA) (extraGenerator,pointB):=by
    refine Or.inr ⟨middleSide,?_,?_,?_⟩
    · exact markedVertex_on_middle (by simp [markedVertices])
    · exact halfTurn_vertexA.symm.trans (middleGenerator_apply vertexA).symm
    · change lowerGenerator=(lowerGenerator*middleGenerator)*middleGenerator
      rw [mul_assoc,middleGenerator_sq,mul_one]
  exact ((pairing.project_eq_iff _ _).mpr
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ h1) (Relation.EqvGen.rel _ _ h2))).symm

theorem right_point_in_any_ball (r:ℝ) (hr:0<r) :
    ∃z:ℍ,z∈polygon.interior ∧dist z vertexA<r := by
  let φ:ℝ→ℍ:=fun t=>⟨(t:ℂ)+Complex.I,by simp⟩
  have hc:Continuous φ:=by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    exact Complex.continuous_ofReal.add continuous_const
  have h0:φ 0=vertexA:=by apply UpperHalfPlane.ext;simp [φ,vertexA]
  have ho:IsOpen (φ⁻¹'Metric.ball vertexA r):=Metric.isOpen_ball.preimage hc
  have hm:0∈φ⁻¹'Metric.ball vertexA r:=by rw [mem_preimage,h0];exact Metric.mem_ball_self hr
  obtain ⟨ε,hε,hsub⟩:=Metric.isOpen_iff.mp ho 0 hm
  refine ⟨φ (ε/2),?_,?_⟩
  · change 0<((ε/2:ℝ):ℂ).re+Complex.I.re
    simp only [Complex.ofReal_re,Complex.I_re,add_zero]
    positivity
  · apply hsub
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0<ε/2)]
    linarith

theorem not_local_tessellation (r:ℝ) (hr:0<r) :
    ¬pairing.LocalTessellation (1,pointA) r := by
  intro ht
  obtain ⟨z,hz,hzr⟩:=right_point_in_any_ball r hr
  have hv:circleMirror z∈polygon.interior:=circleMirror_right_image ▸ mem_image_of_mem _ hz
  let u:polygon.Point:=⟨z,polygon.interior_subset_carrier hz⟩
  let v:polygon.Point:=⟨circleMirror z,polygon.interior_subset_carrier hv⟩
  have huW:(1,u)∈pairing.copyNeighborhood (1,pointA) r:=⟨(1,pointA),rfl,rfl,hzr⟩
  have hvW:(extraGenerator,v)∈pairing.copyNeighborhood (1,pointA) r:=by
    refine ⟨(extraGenerator,pointB),extra_center_glued,rfl,?_⟩
    change dist (circleMirror z) vertexB<r
    rw [←circleMirror_vertexA,circleMirror.isometry.dist_eq]
    exact hzr
  have he:pairing.copyEvaluation (extraGenerator,v)=pairing.copyEvaluation (1,u):=by
    change extraGenerator•circleMirror z=(1:pairing.Generated)•z
    rw [extraGenerator_apply,circleMirror_involutive,one_smul]
  have hq:pairing.project (extraGenerator,v)=pairing.project (1,u):=
    (ht.fiber_eq (1,u) huW (extraGenerator,v)).mpr ⟨hvW,he⟩
  have hi:=pairing.gluing_interior_rigid ((pairing.project_eq_iff _ _).mp hq) (Or.inr hz)
  exact extraGenerator_ne_one (congrArg Prod.fst hi)

theorem not_finiteFiberLocalTessellationCondition : ¬pairing.FiniteFiberLocalTessellationCondition := by
  intro h
  obtain ⟨r,hr,hAll⟩:=h.local_radius pointA
  exact not_local_tessellation r hr (hAll r hr le_rfl)

open scoped Complex.UnitDisc

def idealZero : 𝕔𝔻 := ⟨(-1:ℂ),by norm_num⟩
def idealInfinity : 𝕔𝔻 := ⟨(1:ℂ),by norm_num⟩
def finiteA : 𝕔𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc vertexA)
def finiteB : 𝕔𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc vertexB)

theorem idealZero_klein : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate idealZero=(-1:ℂ) := by
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein idealZero):ℂ)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed idealZero (by change ‖(-1:ℂ)‖=1;norm_num)]
  rfl

theorem idealInfinity_klein : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate idealInfinity=(1:ℂ) := by
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein idealInfinity):ℂ)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed idealInfinity (by change ‖(1:ℂ)‖=1;norm_num)]
  rfl

theorem finiteA_klein : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate finiteA=0 := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate vertexA=0
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit]
  apply Complex.ext <;>norm_num [vertexA]

theorem finiteB_klein : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate finiteB=(15/17:ℂ) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate vertexB=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit]
  apply Complex.ext <;>norm_num [vertexB]

def sideStart (i:Fin 3):𝕔𝔻:=![idealZero,finiteA,finiteB] i
def sideEnd (i:Fin 3):𝕔𝔻:=![finiteA,finiteB,idealInfinity] i

theorem real_segment_mem (a b:ℝ) (hab:a<b) (z:ℂ) :
    z∈segment ℝ (a:ℂ) (b:ℂ) ↔z.im=0 ∧a≤z.re ∧z.re≤b := by
  rw [segment_eq_image_lineMap]
  have he (t:ℝ):AffineMap.lineMap (a:ℂ) (b:ℂ) t=((1-t)*a+t*b:ℝ):=by
    apply Complex.ext <;>simp [AffineMap.lineMap_apply];ring
  constructor
  · rintro ⟨t,ht,rfl⟩
    rw [he]
    simp only [Complex.ofReal_re,Complex.ofReal_im]
    refine ⟨trivial,?_,?_⟩ <;>nlinarith [ht.1,ht.2]
  · rintro ⟨him,hlo,hhi⟩
    refine ⟨(z.re-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hab).le,
      (div_le_one (sub_pos.mpr hab)).mpr (by linarith)⟩,?_⟩
    rw [he]
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      field_simp
      ring
    · simpa only [Complex.ofReal_im] using him.symm

theorem native_side_klein (p q:𝕔𝔻) (z:ℍ) : z∈_root_.LowDimensionalTopology.Geometry.Polygon.nativeCompactifiedSide p q ↔
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) := by
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image).symm

theorem side_intervals (i:Fin 3) : sideSet i=_root_.LowDimensionalTopology.Geometry.Polygon.nativeCompactifiedSide (sideStart i) (sideEnd i) := by
  ext z
  rw [native_side_klein]
  have hd:0<z.re^2+z.im^2+1:=by positivity
  have hz2:0<z.im:=z.im_pos
  have hImag:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z).im=0 ↔z.re=0:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit]
    change -2*z.re/(z.re^2+z.im^2+1)=0 ↔z.re=0
    rw [div_eq_zero_iff]
    constructor
    · rintro (h|h)
      · linarith
      · exact (hd.ne' h).elim
    · intro h
      exact Or.inl (by rw [h,mul_zero])
  have hReal (hr:z.re=0) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z).re=(z.im^2-1)/(z.im^2+1):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit]
    norm_num [hr]
  have hyD:0<z.im^2+1:=by positivity
  fin_cases i
  · change (z.re=0 ∧z.im≤1) ↔_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z∈
      segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        idealZero) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate finiteA)
    rw [idealZero_klein,finiteA_klein,
      show (-1:ℂ)=((-1:ℝ):ℂ) by norm_num,show (0:ℂ)=((0:ℝ):ℂ) from rfl,
      real_segment_mem (-1) 0 (by norm_num),hImag]
    constructor
    · rintro ⟨hr,hi⟩
      refine ⟨hr,?_,?_⟩
      · rw [hReal hr]
        apply (le_div_iff₀ hyD).mpr
        nlinarith
      · rw [hReal hr]
        apply (div_le_iff₀ hyD).mpr
        nlinarith
    · rintro ⟨hr,hlo,hhi⟩
      rw [hReal hr] at hhi
      have hq:= (div_le_iff₀ hyD).mp hhi
      exact ⟨hr,by nlinarith⟩

  · change (z.re=0 ∧1≤z.im ∧z.im≤4) ↔_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z∈
      segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        finiteA) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate finiteB)
    rw [finiteA_klein,finiteB_klein,show (0:ℂ)=((0:ℝ):ℂ) from rfl,
      show (15/17:ℂ)=((15/17:ℝ):ℂ) by norm_num,
      real_segment_mem 0 (15/17) (by norm_num),hImag]
    constructor
    · rintro ⟨hr,hlo,hhi⟩
      refine ⟨hr,?_,?_⟩
      · rw [hReal hr]
        exact div_nonneg (by nlinarith) hyD.le
      · rw [hReal hr]
        apply (div_le_iff₀ hyD).mpr
        nlinarith
    · rintro ⟨hr,hlo,hhi⟩
      rw [hReal hr] at hlo hhi
      have hqlo:= (le_div_iff₀ hyD).mp hlo
      have hqhi:= (div_le_iff₀ hyD).mp hhi
      exact ⟨hr,by nlinarith,by nlinarith⟩
  · change (z.re=0 ∧4≤z.im) ↔_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z∈
      segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        finiteB) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate idealInfinity)
    rw [finiteB_klein,idealInfinity_klein,show (15/17:ℂ)=((15/17:ℝ):ℂ) by norm_num,
      show (1:ℂ)=((1:ℝ):ℂ) from rfl,
      real_segment_mem (15/17) 1 (by norm_num),hImag]
    constructor
    · rintro ⟨hr,hi⟩
      refine ⟨hr,?_,?_⟩
      · rw [hReal hr]
        apply (le_div_iff₀ hyD).mpr
        nlinarith
      · rw [hReal hr]
        apply (div_le_iff₀ hyD).mpr
        nlinarith
    · rintro ⟨hr,hlo,hhi⟩
      rw [hReal hr] at hlo
      have hq:= (le_div_iff₀ hyD).mp hlo
      exact ⟨hr,by nlinarith⟩

theorem sideSet_injective : Function.Injective sideSet := by
  intro i j hij
  have hA:=congrArg (fun s:Set ℍ=>vertexA∈s) hij
  have hB:=congrArg (fun s:Set ℍ=>vertexB∈s) hij
  fin_cases i <;>fin_cases j
  all_goals try rfl
  all_goals try norm_num [sideSet,vertexA,vertexB] at hA
  all_goals norm_num [sideSet,vertexA,vertexB] at hB

def sideIndex : Fin 3≃polygon.Side:=Equiv.ofBijective
  (fun i=>⟨sideSet i,mem_range_self i⟩) ⟨fun _ _ h=>sideSet_injective (congrArg Subtype.val h),by
    intro s
    obtain ⟨i,hi⟩:=s.property
    exact ⟨i,Subtype.ext hi⟩⟩

theorem side_endpoint_ne (i:Fin 3) : sideStart i≠sideEnd i := by
  intro he
  have h:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate he
  fin_cases i <;>norm_num [sideStart,sideEnd,idealZero_klein,idealInfinity_klein,
    finiteA_klein,finiteB_klein] at h

theorem axis_point_eq_A {z:ℍ} (hr:z.re=0) (hi:z.im=1) : z=vertexA := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change z.re=vertexA.re
    norm_num [vertexA]
    exact hr
  · change z.im=vertexA.im
    norm_num [vertexA]
    exact hi

theorem axis_point_eq_B {z:ℍ} (hr:z.re=0) (hi:z.im=4) : z=vertexB := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change z.re=vertexB.re
    norm_num [vertexB]
    exact hr
  · change z.im=vertexB.im
    norm_num [vertexB]
    exact hi

theorem side_intersection_endpoint (i j:Fin 3) (hij:i≠j) (z:ℍ)
    (hi:z∈sideSet i) (hj:z∈sideSet j) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈({sideStart i,sideEnd i}:Set 𝕔𝔻) := by
  fin_cases i <;>fin_cases j
  · exact (hij rfl).elim
  · have he:z=vertexA:=axis_point_eq_A hi.1 (by have:=hi.2;have:=hj.2.1;linarith)
    subst z
    exact Or.inr rfl
  · have:=hi.2;have:=hj.2;linarith
  · have he:z=vertexA:=axis_point_eq_A hi.1 (by have:=hi.2.1;have:=hj.2;linarith)
    subst z
    exact Or.inl rfl
  · exact (hij rfl).elim
  · have he:z=vertexB:=axis_point_eq_B hi.1 (by have:=hi.2.2;have:=hj.2;linarith)
    subst z
    exact Or.inr rfl
  · have:=hi.2;have:=hj.2;linarith
  · have he:z=vertexB:=axis_point_eq_B hi.1 (by have:=hi.2;have:=hj.2.2;linarith)
    subst z
    exact Or.inl rfl
  · exact (hij rfl).elim

def geometricSides : _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicSideIntervals polygon where
  startPoint s:=sideStart (sideIndex.symm s)
  endPoint s:=sideEnd (sideIndex.symm s)
  endpoint_ne s:=side_endpoint_ne _
  side_eq s:=by
    have hi:=congrArg Subtype.val (sideIndex.apply_symm_apply s)
    exact hi.symm.trans (side_intervals _)
  locallyFinite:=by
    let : Finite polygon.Side:=Finite.of_surjective sideIndex sideIndex.surjective
    exact locallyFinite_of_finite _
  side_intersection:=by
    intro s t hst z hzs hzt
    obtain ⟨i,rfl⟩:=sideIndex.surjective s
    obtain ⟨j,rfl⟩:=sideIndex.surjective t
    simpa only [sideIndex.symm_apply_apply] using
      side_intersection_endpoint i j (fun h=>hst (congrArg sideIndex h)) z hzs hzt

theorem native_finite_point_injective : Function.Injective
    (fun z:ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective

theorem native_finite_ne_idealZero (z:ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)≠idealZero := by
  intro h
  have hn:(‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    z):ℂ)‖:ℝ)<1:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z).norm_lt_one
  rw [h] at hn
  change ‖(-1:ℂ)‖<1 at hn
  norm_num at hn

theorem native_finite_ne_idealInfinity (z:ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)≠idealInfinity := by
  intro h
  have hn:(‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    z):ℂ)‖:ℝ)<1:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z).norm_lt_one
  rw [h] at hn
  change ‖(1:ℂ)‖<1 at hn
  norm_num at hn

theorem geometric_vertices : geometricSides.vertices={vertexA,vertexB} := by
  ext z
  constructor
  · intro hz
    obtain ⟨s,hs⟩:=mem_iUnion.mp hz
    obtain ⟨i,rfl⟩:=sideIndex.surjective s
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈
      ({sideStart (sideIndex.symm (sideIndex i)),sideEnd (sideIndex.symm (sideIndex i))}:Set 𝕔𝔻) at hs
    rw [sideIndex.symm_apply_apply] at hs
    fin_cases i
    · rcases hs with h|h
      · exact (native_finite_ne_idealZero z h).elim
      · exact Or.inl (native_finite_point_injective h)
    · rcases hs with h|h
      · exact Or.inl (native_finite_point_injective h)
      · exact Or.inr (native_finite_point_injective h)
    · rcases hs with h|h
      · exact Or.inr (native_finite_point_injective h)
      · exact (native_finite_ne_idealInfinity z h).elim
  · rintro (rfl|rfl)
    · refine mem_iUnion.mpr ⟨sideIndex 0,?_⟩
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc vertexA)∈
        ({sideStart (sideIndex.symm (sideIndex 0)),sideEnd (sideIndex.symm (sideIndex 0))}:Set 𝕔𝔻)
      rw [sideIndex.symm_apply_apply]
      exact Or.inr rfl
    · refine mem_iUnion.mpr ⟨sideIndex 1,?_⟩
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc vertexB)∈
        ({sideStart (sideIndex.symm (sideIndex 1)),sideEnd (sideIndex.symm (sideIndex 1))}:Set 𝕔𝔻)
      rw [sideIndex.symm_apply_apply]
      exact Or.inr rfl

theorem geometric_marked_vertices : {p:polygon.Point|p.val∈geometricSides.vertices}=markedVertices := by
  ext x
  rw [geometric_vertices]
  constructor
  · rintro (h|h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl|rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem weak_geometric_vertex_condition :
    pairing.FiniteVertexCycleCondition {p:polygon.Point|p.val∈geometricSides.vertices} := by
  rw [geometric_marked_vertices]
  exact weak_vertex_condition
def halfDiscBody:Set ℂ:=Metric.closedBall 0 1 ∩{z:ℂ|z.im≤0}
def halfDiscCurve:Set ℂ:=frontier halfDiscBody

theorem halfDiscBody_convex : Convex ℝ halfDiscBody :=
  (convex_closedBall (0:ℂ) 1).inter
    (convex_halfSpace_le Complex.imCLM.toLinearMap.isLinear 0)

theorem halfDiscBody_compact : IsCompact halfDiscBody :=
  (isCompact_closedBall (0:ℂ) 1).inter_right (isClosed_le Complex.continuous_im continuous_const)

theorem halfDiscBody_interior : interior halfDiscBody=
    Metric.ball (0:ℂ) 1 ∩{z:ℂ|z.im<0} := by
  rw [halfDiscBody,interior_inter,interior_closedBall _ (by norm_num : (1:ℝ)≠0)]
  congr 1
  change interior (Complex.im⁻¹'Iic 0)=Complex.im⁻¹'Iio 0
  rw [Complex.interior_preimage_im,interior_Iic]

theorem halfDiscBody_interior_nonempty : (interior halfDiscBody).Nonempty := by
  rw [halfDiscBody_interior]
  refine ⟨-Complex.I/2,?_,?_⟩ <;>norm_num [Metric.mem_ball,dist_zero_right,norm_div]

theorem halfDiscCurve_isJordan : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve halfDiscCurve := by
  obtain ⟨h,_,_,hF⟩:=exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    halfDiscBody_convex halfDiscBody_interior_nonempty halfDiscBody_compact.isBounded
  let A:↥halfDiscCurve≃ₜCircle:=(h.isEmbedding.homeomorphImage (frontier halfDiscBody)).trans
    (Homeomorph.setCongr hF)
  let γ:Circle→ℂ:=fun z=>(A.symm z).val
  have hγ:Continuous γ:=continuous_subtype_val.comp A.symm.continuous
  have hi:Function.Injective γ:=Subtype.val_injective.comp A.symm.injective
  have hR:range γ=halfDiscCurve:=by
    apply subset_antisymm
    · rintro _ ⟨z,rfl⟩
      exact (A.symm z).property
    · intro z hz
      exact ⟨A ⟨z,hz⟩,congrArg Subtype.val (A.symm_apply_apply _)⟩
  rw [←hR]
  exact _root_.LowDimensionalTopology.Geometry.Polygon.isComplexJordanCurve_of_continuous_injective hγ hi

theorem compact_body_jordanInside (K:Set ℂ) (hk:IsCompact K)
    (hne:(interior K).Nonempty) (hJ:_root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve (frontier K)) :
    _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside (frontier K)=interior K := by
  have hcover (A:Set ℂ) (hA:A⊆(frontier K)ᶜ):A⊆interior K ∪Kᶜ:=by
    intro z hz
    by_cases hi:z∈interior K
    · exact Or.inl hi
    · right
      intro hK
      exact hA hz ⟨subset_closure hK,hi⟩
  have hd:Disjoint (interior K) Kᶜ:=disjoint_compl_right.mono_left interior_subset
  have hSubset:interior K⊆_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside (frontier K):=by
    intro z hz
    let C:=connectedComponentIn (frontier K)ᶜ z
    have hn:z∉frontier K:=by rintro ⟨_,hn⟩;exact hn hz
    have hSub:C⊆K:=by
      apply (isPreconnected_connectedComponentIn.subset_left_of_subset_union
        isOpen_interior hk.isClosed.isOpen_compl hd
        (hcover C (connectedComponentIn_subset _ _))
        ⟨z,mem_connectedComponentIn hn,hz⟩).trans interior_subset
    have hb:Bornology.IsBounded C:=hk.isBounded.subset hSub
    let e:=_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanPlaneHomeomorph
    change e z∉e ''frontier K ∧Bornology.IsBounded (connectedComponentIn (e ''frontier K)ᶜ (e z))
    constructor
    · intro he
      exact hn (e.injective.mem_set_image.mp he)
    · have he:connectedComponentIn (e ''frontier K)ᶜ (e z)=e ''C:=by
        rw [←e.image_compl,e.image_connectedComponentIn]
        exact hn
      rw [he]
      exact Complex.orthonormalBasisOneI.repr.isometry.lipschitzWith.isBounded_image hb
  apply subset_antisymm
  · have hI:_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside (frontier K)⊆(frontier K)ᶜ:=by
      intro z hz
      have h:= (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hJ).2.2.2.1
      rw [←h]
      exact Or.inl hz
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions
      hJ).2.2.2.2.1.isPreconnected.subset_left_of_subset_union
      isOpen_interior hk.isClosed.isOpen_compl hd (hcover _ hI)
      ⟨hne.choose,hSubset hne.choose_spec,hne.choose_spec⟩
  · exact hSubset

theorem halfDiscCurve_inside : _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside halfDiscCurve=
    Metric.ball (0:ℂ) 1 ∩{z:ℂ|z.im<0} := by
  rw [halfDiscCurve,compact_body_jordanInside halfDiscBody
    halfDiscBody_compact halfDiscBody_interior_nonempty halfDiscCurve_isJordan,halfDiscBody_interior]

open scoped UpperHalfPlane Complex.UnitDisc

theorem cayley_im (z:ℍ) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ).im=
    -2*z.re/(z.re^2+(z.im+1)^2) := by
  change (((z:ℂ)-Complex.I)/((z:ℂ)+Complex.I)).im=_
  simp only [Complex.div_im,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.I_re,Complex.I_im,sub_zero,add_zero,Complex.normSq_apply,
    UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

theorem cayley_im_neg_iff (z:ℍ) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ).im<0 ↔0<z.re := by
  have hd:0<z.re^2+(z.im+1)^2:=by nlinarith [sq_nonneg z.re,z.im_pos]
  rw [cayley_im,div_lt_iff₀ hd]
  constructor <;>intro h <;>nlinarith

theorem cayley_im_zero_iff (z:ℍ) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ).im=0 ↔z.re=0 := by
  have hd:0<z.re^2+(z.im+1)^2:=by nlinarith [sq_nonneg z.re,z.im_pos]
  rw [cayley_im,div_eq_zero_iff]
  constructor
  · rintro (h|h)
    · linarith
    · exact (hd.ne' h).elim
  · intro h
    exact Or.inl (by rw [h,mul_zero])

theorem halfDiscCurve_bound : halfDiscCurve⊆Metric.closedBall (0:ℂ) 1 := by
  intro z hz
  have hb:=frontier_subset_closure hz
  rw [halfDiscBody_compact.isClosed.closure_eq] at hb
  exact hb.1

theorem halfDiscCurve_native_inside : _root_.LowDimensionalTopology.Geometry.Polygon.nativeJordanInside halfDiscCurve={z:ℍ|0<z.re} := by
  ext z
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside halfDiscCurve ↔_
  rw [halfDiscCurve_inside]
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    z:ℂ)∈Metric.ball (0:ℂ) 1 ∧(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ).im<0 ↔_
  have hz:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ)∈Metric.ball (0:ℂ) 1:=
    mem_ball_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z).norm_lt_one
  rw [and_iff_right hz,cayley_im_neg_iff]
  rfl

theorem halfDiscCurve_native_boundary :
    (fun z:ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ))⁻¹'halfDiscCurve={z:ℍ|z.re=0} := by
  ext z
  have hz:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ)∈Metric.ball (0:ℂ) 1:=
    mem_ball_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z).norm_lt_one
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ)∈frontier halfDiscBody ↔_
  rw [frontier,halfDiscBody_compact.isClosed.closure_eq,halfDiscBody_interior]
  change (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ)∈Metric.closedBall (0:ℂ) 1
    ∧(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ).im≤0) ∧
    ¬((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ)∈Metric.ball (0:ℂ) 1
      ∧(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ).im<0)) ↔z.re=0
  rw [and_iff_right (Metric.ball_subset_closedBall hz),and_iff_right hz]
  constructor
  · rintro ⟨hlo,hhi⟩
    exact (cayley_im_zero_iff z).mp (le_antisymm hlo (not_lt.mp hhi))
  · intro hr
    have hi: (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z:ℂ).im=0:=(cayley_im_zero_iff z).mpr hr
    rw [hi]
    norm_num


def sourcePolygon : _root_.LowDimensionalTopology.Geometry.Polygon.NativeJordanGeodesicPolygon where
  polygon:=polygon
  curve:=halfDiscCurve
  jordan:=halfDiscCurve_isJordan
  contained:=halfDiscCurve_bound
  interior_eq:=halfDiscCurve_native_inside.symm
  boundary_eq:=polygon_boundary.trans halfDiscCurve_native_boundary.symm
  sideIntervals:=geometricSides

theorem nativeJordan_weak_vertex_cycles_not_finiteFiberLocalTessellationCondition :
    ∃J:_root_.LowDimensionalTopology.Geometry.Polygon.NativeJordanGeodesicPolygon,∃S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) J.polygon,
      S.FiniteVertexCycleCondition {p:J.polygon.Point|p.val∈J.sideIntervals.vertices} ∧
      (∀s:J.polygon.Side,∀z∈s.val,z∉J.sideIntervals.vertices→S.OppositeSideNeighborhoods s z) ∧
      ¬S.FiniteFiberLocalTessellationCondition := by
  exact ⟨sourcePolygon,pairing,weak_geometric_vertex_condition,
    (fun s z _ _=>opposite_sides s z),not_finiteFiberLocalTessellationCondition⟩

theorem no_uniform_raw_radius (ε:ℝ) : ¬pairing.UniformLocalTessellationRadius ε := by
  intro h
  exact not_local_tessellation ε h.1 (h.2 pointA ε h.1 le_rfl)

theorem no_natural_vertex_condition : ¬pairing.NaturalVertexCycleCondition geometricSides.vertices := by
  intro h
  apply not_finiteFiberLocalTessellationCondition
  exact _root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_natural_cycles_local_tessellation halfDiscCurve halfDiscCurve_isJordan
    halfDiscCurve_bound halfDiscCurve_native_inside.symm
    (polygon_boundary.trans halfDiscCurve_native_boundary.symm) geometricSides pairing h
    (fun s z _ _=>opposite_sides s z)

theorem not_fundamentalDomain :
    ¬_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain pairing.Generated ℍ MeasureTheory.volume polygon.interior := by
  intro hD
  let z:ℍ:=⟨1+Complex.I,by norm_num⟩
  have hz:z∈polygon.interior:=by norm_num [z,polygon]
  have hv:circleMirror z∈polygon.interior:=circleMirror_right_image ▸mem_image_of_mem _ hz
  have hq:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection pairing.Generated ℍ (circleMirror z)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection pairing.Generated ℍ z:=by
    exact Quotient.sound ⟨extraGenerator,extraGenerator_apply z⟩
  have he:=congrArg UpperHalfPlane.re (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.eq_of_mem _ _ hD hv hz hq)
  rw [circleMirror_re] at he
  norm_num [z] at he

end LowDimensionalTopology.Geometry.Fuchsian.RawVertexCounterexample
