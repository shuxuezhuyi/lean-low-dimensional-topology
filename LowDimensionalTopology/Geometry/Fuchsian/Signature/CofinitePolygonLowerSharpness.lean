/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Euclidean.Angle.PositiveCone
public import LowDimensionalTopology.Geometry.Polygon.Tangential.PolygonTangentialPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegularPolygon.RegularPolygonCycles
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.IdealPolygonNativeGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalSideOrientation
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedSegmentTransport
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals
public import Mathlib.Tactic
public import Mathlib.Data.List.GetD
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CompactPolygonTranslates
public import LowDimensionalTopology.Geometry.Polygon.Area.PolygonArea
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeConformalSingularPoints
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleEllipticClasses
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSupergroups
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ParabolicFundamentalBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicArea
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Data.Fintype.Fin
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaFirstKind
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianElementary
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Transversals
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeSideEndpointTransport
public import LowDimensionalTopology.Geometry.Polygon.Development.LabeledNaturalVertexCycles
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareCompactDevelopment
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.FiniteAreaIdealBoundary
public import LowDimensionalTopology.Geometry.Polygon.Development.NativeDevelopingPoincare
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Development.FinitePolygonPoincareData
public import LowDimensionalTopology.Geometry.Polygon.Development.IdealPolygonPoincareData
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ConvexBoundaryMateCriterion
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.ParabolicFiniteArea
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawCuspClasses
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.DiscPolygonConjugation
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CompactifiedPolygonSides
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.ParabolicSideNormalizers
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonVertexConventions
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.ThreeMarkedSignatureRigidity
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicAngularArea
/-!
# Sharp side counts for cofinite Fuchsian polygons

Tangential polygons realize prescribed genus, elliptic orders and cusps. Their
side pairings retain order-two midpoint marks and the resulting refined sides.
Finite angular cycles give compact realizations; explicit ideal-corner sections
supply the cusp case. The construction identifies the actual quotient signature,
physical area and side count of the generated group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
open scoped OnePoint
open Set InnerProductGeometry Filter Topology
open scoped Complex.UnitDisc UpperHalfPlane Pointwise MatrixGroups ComplexConjugate NNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- Zero denotes a cusp; a positive entry is the original finite cone order. -/
def cofiniteConstructionConeAngle (m : ℕ) : ℝ := 2*Real.pi/(m:ℝ)

/-- The full original deficit, with the last mark retained as the base cycle. -/
def cofiniteConstructionDeficit (g : ℕ) (ms : List ℕ) (last : ℕ) : ℝ :=
  2*(g:ℝ)-2+(ms.length+1:ℕ)-
    ((ms.map (fun m : ℕ => (1:ℝ)/(m:ℝ))).sum+1/(last:ℝ))

def cofiniteConstructionBaseAngle (g : ℕ) (ms : List ℕ) (last : ℕ) : ℝ :=
  cofiniteConstructionConeAngle last/(4*g+ms.length:ℕ)

/-- A marked order-two midpoint is omitted from the strict polygon and will be
recovered by the actual self-side subdivision. Every other outer corner remains. -/
def cofiniteConstructionAngles (g : ℕ) (ms : List ℕ) (last : ℕ) : List ℝ :=
  List.replicate (4*g) (cofiniteConstructionBaseAngle g ms last) ++
    ms.flatMap (fun m => [cofiniteConstructionBaseAngle g ms last] ++
      if m=2 then [] else [cofiniteConstructionConeAngle m])

theorem cofiniteConstruction_base_count (g : ℕ) (ms : List ℕ) (last : ℕ)
    (h : 0<cofiniteConstructionDeficit g ms last) : 2≤4*g+ms.length := by
  have hsum : 0≤(ms.map (fun m : ℕ => (1:ℝ)/(m:ℝ))).sum :=
    List.sum_nonneg (by intro x hx; obtain ⟨m,_,rfl⟩:=List.mem_map.mp hx; positivity)
  have hlast : 0≤(1:ℝ)/(last:ℝ) := by positivity
  by_contra hn
  have hg:g=0:=by omega
  have hm:ms.length≤1:=by omega
  have hm':(ms.length:ℝ)≤1:=by exact_mod_cast hm
  simp only [cofiniteConstructionDeficit,hg,Nat.cast_zero,mul_zero,
    Nat.cast_add,Nat.cast_one] at h
  linarith

theorem cofiniteConstruction_base_mem (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hlast:last=0 ∨ 2≤last) (h : 0<cofiniteConstructionDeficit g ms last) :
    cofiniteConstructionBaseAngle g ms last∈Ico (0:ℝ) Real.pi := by
  have hB:=cofiniteConstruction_base_count g ms last h
  have hBr:(2:ℝ)≤(4*g+ms.length:ℕ):=by exact_mod_cast hB
  have hlastle:cofiniteConstructionConeAngle last≤Real.pi:=by
    rcases hlast with rfl|hlast
    · simp [cofiniteConstructionConeAngle,Real.pi_pos.le]
    · have hlast':(2:ℝ)≤last:=by exact_mod_cast hlast
      apply (div_le_iff₀ (by linarith only [hlast']:(0:ℝ)<last)).mpr
      nlinarith only [Real.pi_pos,hlast']
  constructor
  · dsimp only [cofiniteConstructionBaseAngle,cofiniteConstructionConeAngle]
    positivity
  · dsimp only [cofiniteConstructionBaseAngle]
    apply (div_lt_iff₀ (by linarith only [hBr]:(0:ℝ)<(4*g+ms.length:ℕ))).mpr
    nlinarith only [Real.pi_pos,hBr,hlastle]

theorem cofiniteConstruction_angles_mem (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hms:∀m∈ms,m=0 ∨ 2≤m) (hlast:last=0 ∨ 2≤last)
    (h : 0<cofiniteConstructionDeficit g ms last) :
    ∀θ∈cofiniteConstructionAngles g ms last,θ∈Ico (0:ℝ) Real.pi := by
  intro θ hθ
  have hbase:=cofiniteConstruction_base_mem g ms last hlast h
  rcases List.mem_append.mp hθ with hθ|hθ
  · exact (List.eq_of_mem_replicate hθ) ▸ hbase
  · obtain ⟨m,hm,hθ⟩:=List.mem_flatMap.mp hθ
    rcases List.mem_append.mp hθ with hθ|hθ
    · simpa only [List.mem_singleton] using (List.mem_singleton.mp hθ) ▸ hbase
    · by_cases hm2:m=2
      · simp only [hm2,ite_true,List.not_mem_nil] at hθ
      · simp only [hm2,ite_false,List.mem_singleton] at hθ
        subst θ
        rcases hms m hm with rfl|hm
        · simp [cofiniteConstructionConeAngle,Real.pi_pos]
        · have hm3:3≤m:=by omega
          have hmr:(3:ℝ)≤m:=by exact_mod_cast hm3
          constructor
          · dsimp only [cofiniteConstructionConeAngle]; positivity
          · dsimp only [cofiniteConstructionConeAngle]
            apply (div_lt_iff₀ (by linarith only [hmr]:(0:ℝ)<m)).mpr
            nlinarith only [Real.pi_pos,hmr]

theorem cofiniteConstruction_angles_defect (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB:0<4*g+ms.length) :
    (((cofiniteConstructionAngles g ms last).length:ℝ)-2)*Real.pi-
      (cofiniteConstructionAngles g ms last).sum=
      2*Real.pi*cofiniteConstructionDeficit g ms last := by
  have hBr:(4*g+ms.length:ℕ)≠(0:ℝ):=by exact_mod_cast (Nat.ne_of_gt hB)
  have hbase:(4*g+ms.length:ℕ)*cofiniteConstructionBaseAngle g ms last=
      cofiniteConstructionConeAngle last:=by
    exact mul_div_cancel₀ _ hBr
  have hs (ls:List ℕ):
      (((ls.flatMap (fun m=>[cofiniteConstructionBaseAngle g ms last]++
        if m=2 then [] else [cofiniteConstructionConeAngle m])).length:ℝ))*Real.pi-
       (ls.flatMap (fun m=>[cofiniteConstructionBaseAngle g ms last]++
        if m=2 then [] else [cofiniteConstructionConeAngle m])).sum=
       (ls.length:ℝ)*(2*Real.pi-cofiniteConstructionBaseAngle g ms last)-
        2*Real.pi*(ls.map (fun m:ℕ=>(1:ℝ)/(m:ℝ))).sum := by
    induction ls with
    | nil => simp
    | cons m ls ih =>
      by_cases hm:m=2
      · subst m
        simp only [List.flatMap_cons,ite_true,List.append_nil,List.length_append,
          List.length_cons,List.length_nil,List.sum_append,List.sum_cons,List.sum_nil,
          List.map_cons,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at *
        dsimp only [cofiniteConstructionConeAngle] at *
        linarith
      · simp only [List.flatMap_cons,hm,ite_false,List.length_append,
          List.length_cons,List.length_nil,List.sum_append,List.sum_cons,List.sum_nil,
          List.map_cons,Nat.cast_add,Nat.cast_one] at *
        dsimp only [cofiniteConstructionConeAngle] at *
        rw [div_eq_mul_inv,one_div] at *
        linarith
  have hh:=hs ms
  simp only [cofiniteConstructionAngles,List.length_append,List.length_replicate,
    List.sum_append,List.sum_replicate,nsmul_eq_mul,Nat.cast_add] at *
  dsimp only [cofiniteConstructionDeficit,cofiniteConstructionConeAngle] at *
  push_cast at *
  simp only [div_eq_mul_inv] at *
  nlinarith only [hh,hbase]

/-- The strict corners of the actual lower-sharpness polygon exist with their
literal requested angles and a genuine common hyperbolic incircle. Pairing and
whole-group conclusions are separate obligations. -/
theorem cofiniteConstruction_polygon_exists (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hms:∀m∈ms,m=0 ∨ 2≤m) (hlast:last=0 ∨ 2≤last)
    (h : 0<cofiniteConstructionDeficit g ms last) :
    ∃Q:_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon (cofiniteConstructionAngles g ms last).length,Q.IsConvex ∧
      (∀i,Q.angle i=(cofiniteConstructionAngles g ms last)[i]) ∧
      ∃d,Q.HasIncircleAt 0 d := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=
    fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]
  apply _root_.LowDimensionalTopology.Geometry.Polygon.exists_tangentialDiscPolygon θ
  · intro i
    exact cofiniteConstruction_angles_mem g ms last hms hlast h _ (List.getElem_mem _)
  · have hB:=cofiniteConstruction_base_count g ms last h
    have hdef:=cofiniteConstruction_angles_defect g ms last (by omega)
    have hs:∑i,θ i=(cofiniteConstructionAngles g ms last).sum:=by
      rw [←List.sum_ofFn]
      apply congrArg List.sum
      exact List.ofFn_getElem
    rw [hs]
    have hp:0<2*Real.pi*cofiniteConstructionDeficit g ms last:=by positivity
    linarith only [hdef,hp]

def cofiniteClosedOrthogonal (L:ℂ≃ₗᵢ[ℝ]ℂ) : 𝕔𝔻≃ₜ𝕔𝔻 where
  toFun z:=Complex.UnitClosedDisc.mk (L (z:ℂ)) (by rw [L.norm_map];exact z.norm_le_one)
  invFun z:=Complex.UnitClosedDisc.mk (L.symm (z:ℂ)) (by rw [L.symm.norm_map];exact z.norm_le_one)
  left_inv z:=by apply Subtype.ext;exact L.symm_apply_apply (z:ℂ)
  right_inv z:=by apply Subtype.ext;exact L.apply_symm_apply (z:ℂ)
  continuous_toFun:=by
    apply Complex.UnitClosedDisc.isEmbedding_coe.continuous_iff.mpr
    exact L.continuous.comp Complex.UnitClosedDisc.continuous_coe
  continuous_invFun:=by
    apply Complex.UnitClosedDisc.isEmbedding_coe.continuous_iff.mpr
    exact L.symm.continuous.comp Complex.UnitClosedDisc.continuous_coe

theorem cofiniteClosedOrthogonal_klein (L:ℂ≃ₗᵢ[ℝ]ℂ) (z:𝕔𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (cofiniteClosedOrthogonal L z)=L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate z) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (L (z:ℂ))=L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z:ℂ))
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,L.norm_map]
  simpa only [Complex.real_smul] using (L.map_smul (2/(1+‖(z:ℂ)‖^2)) (z:ℂ)).symm

def cofiniteTangentMirror {n:ℕ} (θ:Fin n→ℝ) (d:ℝ) (i j:Fin n) : ℂ≃ₗᵢ[ℝ]ℂ :=
  _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (Circle.exp
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (i.val+1)+_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (j.val+1))) true

theorem cofiniteTangentMirror_unit {n:ℕ} (θ:Fin n→ℝ) (d:ℝ) (i j:Fin n) (t:ℝ) :
    cofiniteTangentMirror θ d i j (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit t)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (i.val+1)+_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (j.val+1)-t) := by
  rw [cofiniteTangentMirror,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply]
  simp only [ite_true,regular_polygonAngleUnit_conj]
  rw [sub_eq_add_neg,regular_polygonAngleUnit_add]
  simp only [Circle.coe_exp,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit,circleMap_zero,Complex.ofReal_one,one_mul]

theorem cofiniteTangentMirror_involutive {n:ℕ} (θ:Fin n→ℝ) (d:ℝ) (i j:Fin n) :
    cofiniteTangentMirror θ d i j*cofiniteTangentMirror θ d i j=1 := by
  rw [cofiniteTangentMirror,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_mul]
  simp only [ite_true,mul_inv_cancel,Bool.xor_self]
  exact _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_one

theorem cofiniteTangentMirror_vertex_left {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (he:θ i=θ (finRotate n j)) :
    cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd (finRotate n j) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
  rw [cofiniteClosedOrthogonal_klein,_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_coordinate,
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_coordinate,map_smul,cofiniteTangentMirror_unit]
  rw [he]
  apply congrArg (fun v:ℂ=>_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate (θ (finRotate n j)) d • v)
  have hi:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_succ θ d i
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle,_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle]
  have hu:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_unit_next θ d hb j
  rw [regular_polygonAngleUnit_add,hu,
    ←regular_polygonAngleUnit_add]
  congr 1
  rw [←he]
  linarith only [hi]

theorem cofiniteTangentMirror_vertex_right {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (he:θ (finRotate n i)=θ j) :
    cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd (finRotate n i))=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd j := by
  have hs:cofiniteTangentMirror θ d j i=cofiniteTangentMirror θ d i j:=by
    dsimp only [cofiniteTangentMirror]
    congr 2
    ring
  have h:=cofiniteTangentMirror_vertex_left θ d hθ hd hb j i he.symm
  rw [hs] at h
  have hh:=congrArg (cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)) h
  have hinv (z:𝕔𝔻):cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)
      (cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j) z)=z:=by
    apply Subtype.ext
    change (cofiniteTangentMirror θ d i j*cofiniteTangentMirror θ d i j) (z:ℂ)=(z:ℂ)
    rw [cofiniteTangentMirror_involutive]
    rfl
  rw [hinv] at hh
  exact hh.symm

/-- Reversed matching endpoint angles give an actual reflection carrying the
entire finite-or-ideal side onto its prescribed partner. -/
theorem cofiniteTangentMirror_side_image {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j) :
    cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j) ''
      _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=
      _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices j := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.image_injective
  have he (k:Fin n):_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ''
      _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices k=
      segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd k))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd (finRotate n k))):=by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    rfl
  calc
    _=cofiniteTangentMirror θ d i j '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ''
        _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i):=by
      rw [image_image,image_image]
      congr 1
      funext z
      exact cofiniteClosedOrthogonal_klein _ z
    _=cofiniteTangentMirror θ d i j ''
        segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i))
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd (finRotate n i))):=by rw [he]
    _=segment ℝ
        (cofiniteTangentMirror θ d i j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)))
        (cofiniteTangentMirror θ d i j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd (finRotate n i)))):=
      image_segment ℝ (cofiniteTangentMirror θ d i j).toLinearEquiv.toAffineEquiv.toAffineMap _ _
    _=segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd (finRotate n j)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd j)):=by
      rw [←cofiniteClosedOrthogonal_klein,←cofiniteClosedOrthogonal_klein,
        cofiniteTangentMirror_vertex_left θ d hθ hd hb i j hl,
        cofiniteTangentMirror_vertex_right θ d hθ hd hb i j hr]
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices j:=by
      rw [he,segment_symm]

theorem cofiniteConstruction_refined_count (g:ℕ) (ms:List ℕ) (last:ℕ) :
    (cofiniteConstructionAngles g ms last).length+ms.count 2=4*g+2*ms.length := by
  have h (ls:List ℕ):
      (ls.flatMap (fun m=>[cofiniteConstructionBaseAngle g ms last]++
        if m=2 then [] else [cofiniteConstructionConeAngle m])).length+ls.count 2=2*ls.length:=by
    induction ls with
    | nil => simp
    | cons m ls ih =>
      by_cases hm:m=2 <;> simp [List.flatMap_cons,hm] at * <;> omega
  have hh:=h ms
  simp only [cofiniteConstructionAngles,List.length_append,List.length_replicate]
  omega

theorem cofiniteTangentMirror_native_commutes {n:ℕ} (θ:Fin n→ℝ) (d:ℝ) (i j:Fin n) (x:ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) x))=
      cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (cofiniteTangentMirror θ d i j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x))))=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  rfl

theorem cofiniteTangentMirror_native_side_image {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j) :
    triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) ''
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) j := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
  have hM:M*M=1:=by
    change triangleVertexOrthogonalHom (cofiniteTangentMirror θ d i j)*
      triangleVertexOrthogonalHom (cofiniteTangentMirror θ d i j)=_
    rw [←map_mul,cofiniteTangentMirror_involutive,map_one]
  have hsubset (k l:Fin n) (hk:θ k=θ (finRotate n l)) (hl:θ (finRotate n k)=θ l):
      triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d k l) '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q k⊆_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q l:=by
    rintro _ ⟨x,hx,rfl⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d k l) x))∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge Q.vertices l
    rw [cofiniteTangentMirror_native_commutes]
    exact (cofiniteTangentMirror_side_image θ d hθ hd hb k l hk hl) ▸ mem_image_of_mem _ hx
  apply subset_antisymm (hsubset i j hl hr)
  intro x hx
  have hs:cofiniteTangentMirror θ d j i=cofiniteTangentMirror θ d i j:=by
    dsimp only [cofiniteTangentMirror]
    congr 2
    ring
  have hy:=hsubset j i hr.symm hl.symm (mem_image_of_mem _ hx)
  rw [hs] at hy
  refine ⟨M x,hy,?_⟩
  change (M*M) x=x
  rw [hM]
  rfl

theorem cofiniteTangentMirror_line_conjugation {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
    M*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i)*M⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q j) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
  obtain ⟨a,ha⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isometry_exists_realGL M.isometry
  have he (x:ℍ):M x=a • x:=congrFun ha x
  have hi (x:ℍ):M.symm x=a⁻¹ • x:=by
    apply M.injective
    rw [M.apply_symm_apply,he,smul_inv_smul]
  obtain ⟨x,hx,y,hy,hxy⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeCompactifiedSide_nontrivial (Q.vertices i)
    (Q.vertices (finRotate n i)) (Q.vertices_injective.ne (Q.next_ne_self i).symm)
  have hside:=cofiniteTangentMirror_native_side_image θ d hθ hd hb i j hl hr
  have hline:(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).realGLMap a=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q j:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_points _ _ (M.injective.ne hxy)
    · rw [(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).realGLMap_carrier]
      exact ⟨x,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hx,(he x).symm⟩
    · rw [(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).realGLMap_carrier]
      exact ⟨y,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hy,(he y).symm⟩
    · exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q j (hside ▸ mem_image_of_mem M hx)
    · exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q j (hside ▸ mem_image_of_mem M hy)
  change M*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i)*M⁻¹=_
  apply IsometryEquiv.ext
  intro z
  change M ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).reflection (M.symm z))=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q j).reflection z
  rw [hi,he,(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).reflection_realGL_conjugation a,hline]

def cofiniteTangentPairingElement {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n) :ℍ≃ᵢℍ:=
  triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)*
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i)

theorem cofiniteTangentPairingElement_inverse {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j) :
    cofiniteTangentPairingElement θ d hθ hd hb j i=
      (cofiniteTangentPairingElement θ d hθ hd hb i j)⁻¹ := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
  let Ri:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i)
  let Rj:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q j)
  have hs:cofiniteTangentMirror θ d j i=cofiniteTangentMirror θ d i j:=by
    dsimp only [cofiniteTangentMirror]
    congr 2
    ring
  have hMi:M⁻¹=M:=by
    apply inv_eq_of_mul_eq_one_left
    change triangleVertexOrthogonalHom (cofiniteTangentMirror θ d i j)*
      triangleVertexOrthogonalHom (cofiniteTangentMirror θ d i j)=1
    rw [←map_mul,cofiniteTangentMirror_involutive,map_one]
  have hRi:Ri⁻¹=Ri:=by
    apply inv_eq_of_mul_eq_one_left
    apply IsometryEquiv.ext
    intro z
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).reflection_involutive z
  have hc:M*Ri*M⁻¹=Rj:=cofiniteTangentMirror_line_conjugation θ d hθ hd hb i j hl hr
  dsimp only [cofiniteTangentPairingElement]
  rw [hs]
  change M*Rj=(M*Ri)⁻¹
  rw [←hc,hMi,mul_inv_rev,hRi,hMi]
  have hMs:M*M=1:=by
    have hh:=congrArg (fun f:ℍ≃ᵢℍ=>f*M) hMi
    simp only [inv_mul_cancel] at hh
    exact hh.symm
  calc
    M*(M*Ri*M)=M*M*Ri*M:=by group
    _=Ri*M:=by rw [hMs,one_mul]

theorem cofiniteTangentPairingElement_side_image {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j) :
    cofiniteTangentPairingElement θ d hθ hd hb i j ''
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) j := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  have he:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_reflection_image Q i
  calc
    _=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) ''
        ((fun z:ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i) z) '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i):=by
      rw [image_image]
      rfl
    _=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i:=by rw [he]
    _=_:=cofiniteTangentMirror_native_side_image θ d hθ hd hb i j hl hr

theorem cofiniteTangentPairingElement_conformal {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n) :
    cofiniteTangentPairingElement θ d hθ hd hb i j∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  let t:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (i.val+1)+_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (j.val+1)
  let u:=Circle.exp (t/2)
  obtain ⟨L,hL⟩:=regular_unit_mirror_exists u
  have hu:u^2=Circle.exp t:=by
    dsimp only [u]
    rw [←Circle.exp_natCast_mul]
    congr 1
    ring
  have hM:triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L:=by
    rw [hL,hu]
    rfl
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i),?_⟩
  apply IsometryEquiv.ext
  intro z
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L _ ) • z=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry _ z)=_
  rw [←hM]
  rfl

/-- The concrete ordered tangent sides carry actual inverse-compatible
orientation-preserving pairing maps, once their finite matching is specified. -/
def cofiniteTangentialSidePairing {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (ρ:Equiv.Perm (Fin n))
    (hρ:Function.Involutive ρ) (hθρ:∀i,θ i=θ (finRotate n (ρ i))) :
    _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let E:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q
  refine { paired:=E.symm.trans (ρ.trans E)
           involutive:=?_
           element:=fun s=>cofiniteTangentPairingElement θ d hθ hd hb (E.symm s) (ρ (E.symm s))
           element_paired:=?_
           side_image:=?_ }
  · intro s
    change E (ρ (E.symm (E (ρ (E.symm s)))))=s
    rw [E.symm_apply_apply,hρ,E.apply_symm_apply]
  · intro s
    change cofiniteTangentPairingElement θ d hθ hd hb (E.symm (E (ρ (E.symm s))))
      (ρ (E.symm (E (ρ (E.symm s)))))=_
    rw [E.symm_apply_apply,hρ]
    apply cofiniteTangentPairingElement_inverse θ d hθ hd hb _ _ (hθρ _)
    simpa only [hρ (E.symm s)] using (hθρ (ρ (E.symm s))).symm
  · intro s
    obtain ⟨i,rfl⟩:=E.surjective s
    change cofiniteTangentPairingElement θ d hθ hd hb (E.symm (E i)) (ρ (E.symm (E i))) ''
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i=(E (ρ (E.symm (E i)))).val
    rw [E.symm_apply_apply]
    apply cofiniteTangentPairingElement_side_image θ d hθ hd hb _ _ (hθρ _)
    simpa only [hρ i] using (hθρ (ρ i)).symm


open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.DiscreteGroups.Action

theorem cofiniteSL_klein_orientation (s:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (p q r:𝔻) :
    0<OriginalOrientation.signedArea
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s p))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s q)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s r)) ↔
    0<OriginalOrientation.signedArea
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate p)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate q)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate r) := by
  have hd:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coefficients_unit s
  have hd':Complex.normSq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientA s)-Complex.normSq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientC s)=1:=by
    simpa only [Complex.normSq_eq_norm_sq] using hd
  have hp:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coefficient_denom_ne_zero hd p
  have hq:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coefficient_denom_ne_zero hd q
  have hr:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coefficient_denom_ne_zero hd r
  change (0<OriginalOrientation.signedArea
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s p))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s q)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s r))) ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action_coe]
  exact OriginalOrientation.fractional_klein_signedArea_pos_iff _ _ p q r hd' hp hq hr

/-- A genuine orientation-preserving centered native map is determined by one
nonzero marked ray point. The reflection ambiguity of an arbitrary isometry
is excluded by its actual determinant-one representative. -/
theorem cofiniteSL_rotation_of_marked_ray (s:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hs:s • UpperHalfPlane.I=UpperHalfPlane.I) (u:Circle)
    (z:𝔻) (hz:(z:ℂ)≠0)
    (hzmap:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s z=circleDiscRotationHom u z) :
    ∀w:𝔻,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s w=circleDiscRotationHom u w := by
  obtain ⟨a,b,hab,rfl⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_fix_I_rotation s hs
  have hmul:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier a b=(u:ℂ):=by
    have h:=congrArg (fun w:𝔻=>(w:ℂ)) hzmap
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL_disc_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation_coe,circleDiscRotationHom_apply] at h
    exact mul_right_cancel₀ hz h
  intro w
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL_disc_action]
  apply Complex.UnitDisc.coe_injective
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier a b*(w:ℂ)=(u:ℂ)*(w:ℂ)
  rw [hmul]

/-- The actual outward tangent foot follows the positively ordered original
boundary; this determinant fixes the chirality of the local corner charts. -/
theorem cofinite_radial_signedArea (r t a b:ℝ) :
    OriginalOrientation.signedArea
      (r • _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit a)
      (t • _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit b) 0=
      r*t*Real.sin (b-a) := by
  simp only [OriginalOrientation.signedArea,zero_sub,map_sub,
    Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
    Complex.smul_re,Complex.smul_im,Complex.conj_re,Complex.conj_im,
    smul_eq_mul,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_re,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_im,Real.sin_sub]
  ring

theorem cofiniteTangential_outgoing_orientation {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) (z:𝔻)
    (hz:_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    0<OriginalOrientation.signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))) 0 := by
  have hzk:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate (θ i) d •
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,←hz,_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_coordinate]
  rw [hzk,_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot_coordinate,_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_unit_next θ d hb i,
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_succ,cofinite_radial_signedArea,_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle]
  rw [show _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i+2*_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d-
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i+_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d)=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d by ring]
  apply mul_pos (mul_pos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_pos (hθ i) hd)
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hd))
  exact Real.sin_pos_of_pos_of_lt_pi (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_bounds (hθ i) hd).1
    (lt_trans (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_bounds (hθ i) hd).2 (by linarith only [Real.pi_pos]))

/-- The ordered imaginary pair normalizer sends its second point to the
positive real radius in the actual Poincare disc. -/
theorem cofinite_normalized_probe (k:ℝ) (hk:1<k) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 k (lt_trans zero_lt_one hk)):ℂ)=
      (((k-1)/(k+1):ℝ):ℂ) := by
  apply Complex.ext
  all_goals
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyFormula,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.div_re,Complex.div_im,
      Complex.normSq_apply]

theorem cofiniteTangential_normalizer {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) (z:𝔻)
    (hz:_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    let f:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)
    ∃s:Matrix.SpecialLinearGroup (Fin 2) ℝ,∃k:ℝ,∃hk:1<k,
      s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z=UpperHalfPlane.I ∧
      s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 k (lt_trans zero_lt_one hk) ∧
      0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s 0:ℂ).im := by
  let f:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)
  have hpos:=cofiniteTangential_outgoing_orientation θ d hθ hd hb i z hz
  change 0<OriginalOrientation.signedArea
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate f) 0 at hpos
  have hne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f:=by
    intro he
    have hzf:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective he
    rw [hzf] at hpos
    exact (lt_irrefl (0:ℝ)) (by
      simpa only [OriginalOrientation.signedArea,sub_self,map_zero,zero_mul,Complex.zero_im] using hpos)
  obtain ⟨s,k,hk,hsz,hsf⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_sl2_normalized_pair (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f) hne
  have hpos':0<OriginalOrientation.signedArea
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s z))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s f)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s 0)):=
    (cofiniteSL_klein_orientation s z f 0).mpr (by
      have hzK:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0:𝔻)=0:=by
        change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (0:ℂ)=0
        simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,mul_zero]
      rw [hzK]
      exact hpos)
  have hsz':_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s z=0:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)=0
    rw [hsz]
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero]
  have hsf':(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s f:ℂ)=(((k-1)/(k+1):ℝ):ℂ):=by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f):ℂ)=_
    rw [hsf,cofinite_normalized_probe k hk]
  have hp:0<(k-1)/(k+1):=div_pos (by linarith only [hk]) (by linarith only [hk])
  refine ⟨s,k,hk,hsz,hsf,?_⟩
  rw [hsz'] at hpos'
  change 0<OriginalOrientation.signedArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (0:ℂ))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s f:ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s 0:ℂ)) at hpos'
  rw [hsf'] at hpos'
  simp only [OriginalOrientation.signedArea,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,mul_zero,sub_zero,
    map_mul,Complex.conj_ofReal,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,add_zero] at hpos'
  have ha:0<2/(1+‖(((k-1)/(k+1):ℝ):ℂ)‖^2):=by positivity
  have hb':0<2/(1+‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s 0:ℂ)‖^2):=by positivity
  have hp':0<(2/(1+‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s 0:ℂ)‖^2))*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action s 0:ℂ).im:=
    (mul_pos_iff_of_pos_left (mul_pos ha hp)).mp hpos'
  exact (mul_pos_iff_of_pos_left hb').mp hp'


open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The actual common incircle gives the distance to each whole support, not
just a distance estimate on the finite polygon edge. -/
theorem cofiniteTangential_support_distance {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) :
    ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb).supportLine i).pointDist 0=d := by
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  let L:=S.supportLine i
  let f:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)
  have hf:f∈L.carrier:=by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_equation_iff _ _ _ _ f).mpr
    change inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate f)=Real.tanh d
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot_coordinate,real_inner_smul_right,
      real_inner_self_eq_norm_sq,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm,one_pow,mul_one]
  have hlower (z:L.carrier):d≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z.val:=by
    have he:inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z.val)=Real.tanh d:=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_equation_iff _ _ _ _ z.val).mp z.property
    have ht:Real.tanh d≤Real.tanh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z.val):=by
      calc
        Real.tanh d=inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i)))
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z.val):=he.symm
        _≤‖_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i))‖*‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z.val‖:=real_inner_le_norm _ _
        _=Real.tanh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z.val):=by
          rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm,one_mul,_root_.LowDimensionalTopology.Geometry.Polygon.kleinCoordinate_norm_eq_tanh_distance]
    have hh:=(Real.artanh_le_artanh_iff ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩
      ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩).mpr ht
    simpa only [Real.artanh_tanh] using hh
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.pointDist_eq_iInf]
  have hbb:BddBelow (range (fun z:L.carrier=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z.val)):=by
    refine ⟨0,?_⟩
    rintro _ ⟨z,rfl⟩
    change 0≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z.val
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
    exact dist_nonneg
  let :Nonempty L.carrier:=⟨⟨f,hf⟩⟩
  apply le_antisymm
  · exact (ciInf_le hbb ⟨f,hf⟩).trans_eq (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot_distance θ d hd _)
  · exact le_ciInf hlower

/-- A finite actual tangential corner contains the actual incircle center in
its proper angle, even when either neighboring vertex is ideal. -/
theorem cofiniteTangential_corner_origin {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) (z:𝔻)
    (hz:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    let C:=((_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb).cornerTriangle i).finiteHalfPlaneCornerAtDiscA z hz
    UpperHalfPlane.I∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior C.rayAB C.rayAC := by
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  let C:=(S.cornerTriangle i).finiteHalfPlaneCornerAtDiscA z hz
  apply (C.mem_interior_iff _).mpr
  have hzero:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=0:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero]
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.halfPlaneCoordinate,hzero] using S.cornerTriangle_origin_coordinates i

/-- The original radial line is the true internal half-angle at every finite
constructed corner; no assumption that the other corners are finite is used. -/
theorem cofiniteTangential_corner_half_angle {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) (z:𝔻)
    (hz:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    let C:=((_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb).cornerTriangle i).finiteHalfPlaneCornerAtDiscA z hz
    ∃hne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z≠UpperHalfPlane.I,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure C.rayAB (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough _ UpperHalfPlane.I hne)=θ i/2 ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure C.rayAC (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough _ UpperHalfPlane.I hne)=θ i/2 := by
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  let T:=S.cornerTriangle i
  let C:=T.finiteHalfPlaneCornerAtDiscA z hz
  have ho:=cofiniteTangential_corner_origin θ d hθ hd hb i z hz
  have hn:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z≠UpperHalfPlane.I:=by
    intro he
    have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior_subset_compl_union C.rayAB C.rayAC ho
    exact h (Or.inl (he ▸ C.rayAB.start_mem))
  let V:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) UpperHalfPlane.I hn
  have hdC:C.rayAB.supportLine.pointDist UpperHalfPlane.I=C.rayAC.supportLine.pointDist UpperHalfPlane.I:=by
    rw [C.supportAB,C.supportAC,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero,
      ←_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.pointDist_eq_halfPlane,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.pointDist_eq_halfPlane,
      S.cornerTriangle_sideC,S.cornerTriangle_sideB]
    rw [cofiniteTangential_support_distance θ d hθ hd hb,
      cofiniteTangential_support_distance θ d hθ hd hb]
  have hbis:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngle_equidistant_bisects C.rayAB C.rayAC C.proper hn ho hdC
  have hadd:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_add_of_mem_proper C.rayAB V C.rayAC C.proper ho
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough_mem _ _ _) hn.symm
  have hang:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure C.rayAB C.rayAC=θ i:=by
    have he:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle θ d hθ hd hb i
    change S.toDiscPolygon.angle i=θ i at he
    rw [S.angle_eq_cornerTriangle,T.alpha_of_finite z hz,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane,T.cornerRayABAtA_toHalfPlane,
      T.cornerRayACAtA_toHalfPlane] at he
    exact he
  refine ⟨hn,?_,?_⟩
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure C.rayAB V=θ i/2
    rw [hang] at hadd
    linarith only [hadd,hbis]
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure C.rayAC V=θ i/2
    rw [hang] at hadd
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm]
    linarith only [hadd,hbis]


open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

theorem cofinite_circle_angle_one_positive (u:Circle) (θ:ℝ)
    (him:0<(u:ℂ).im) (hθ:angle (1:ℂ) (u:ℂ)=θ) :
    u=Circle.exp θ := by
  rw [Complex.angle_one_left u.coe_ne_zero,
    abs_of_nonneg (Complex.arg_nonneg_iff.mpr him.le)] at hθ
  rw [←hθ]
  exact (Circle.exp_arg u).symm

/-- A genuine forward ray containing a positive real disc point has exactly
the positive real unit direction; its full line alone would not suffice. -/
theorem cofinite_centered_ray_unit (R:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt UpperHalfPlane.I)
    (x:ℍ) (hx:x∈R.val) (hxI:x≠UpperHalfPlane.I)
    (t:ℝ) (ht:0<t) (hxt:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:ℂ)=(t:ℂ)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection R=1 := by
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_I_cayley R R hx hxI
    R.directionPoint_mem.1 R.directionPoint_mem.2
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_self,hxt] at h
  obtain ⟨_,a,ha,he⟩:=angle_eq_zero_iff.mp h.symm
  have hrep:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc R.directionPoint:ℂ)=((a*t:ℝ):ℂ):=by
    rw [he,Complex.real_smul]
    push_cast
    rfl
  change _root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc R.directionPoint:ℂ),triangleVertexTip_ne_zero R⟩=1
  have hz:(⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc R.directionPoint:ℂ),triangleVertexTip_ne_zero R⟩:{z:ℂ//z≠0})=
      ⟨((a*t:ℝ):ℂ)*(1:Circle),mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos ha ht).ne') (1:Circle).coe_ne_zero⟩:=
    Subtype.ext (by simpa only [Circle.coe_one,mul_one] using hrep)
  rw [hz,_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection_radial (a*t) (mul_pos ha ht)]

/-- In the actual centered coordinate, the positively ordered proper corner
is the standard angular cone. Chirality is witnessed by a true interior point. -/
theorem cofinite_centered_corner_cone (R S:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt UpperHalfPlane.I)
    (hne:R.supportLine≠S.supportLine) (θ:ℝ)
    (hθ:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S=θ) (hR:_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection R=1)
    (q:ℍ) (hq:q∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S)
    (him:0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc q:ℂ).im) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection S=Circle.exp θ ∧
      ∀x:ℍ,x∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S) ↔
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:ℂ)∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp θ:ℂ)} := by
  obtain ⟨a,ha,hRa⟩:=triangleVertex_kleinDirection_unit R
  obtain ⟨b,hb,hSb⟩:=triangleVertex_kleinDirection_unit S
  have hcone (x:ℍ):x∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S) ↔
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:ℂ)∈Submodule.span ℝ≥0
        {(_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection R:ℂ),(_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection S:ℂ)}:=by
    have he:x∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S) ↔
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S):=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.mem_set_image.symm
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayley_closure_properHAngleInterior_I R S hne] at he
    change x∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S) ↔
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:ℂ)∈Submodule.span ℝ≥0 {R.kleinDirection,S.kleinDirection} at he
    rw [hRa,hSb] at he
    exact he.trans (_root_.LowDimensionalTopology.Geometry.Euclidean.positiveCone_span_smul_mem_iff a b ha hb)
  have hqC: (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc q:ℂ)∈Submodule.span ℝ≥0
      {(1:ℂ),(_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection S:ℂ)}:=by
    simpa only [hR,Circle.coe_one] using (hcone q).mp (subset_closure hq)
  obtain ⟨c,d,he⟩:=Submodule.mem_span_pair.mp hqC
  have heI: (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc q:ℂ).im=(d:ℝ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection S:ℂ).im:=by
    have h:=congrArg Complex.im he
    change ((c:ℝ) • (1:ℂ)+(d:ℝ) • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection S:ℂ)).im=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc q:ℂ).im at h
    simpa only [Complex.add_im,Complex.smul_im,Complex.one_im,smul_eq_mul,mul_zero,zero_add] using h.symm
  have hSpos:0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection S:ℂ).im:=by
    rw [heI] at him
    by_contra hn
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos d.property (not_lt.mp hn))) him
  have hSU:_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection S=Circle.exp θ:=by
    apply cofinite_circle_angle_one_positive _ θ hSpos
    simpa only [hR,Circle.coe_one] using (_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection_angle R S).trans hθ
  refine ⟨hSU,?_⟩
  intro x
  simpa only [hR,hSU,Circle.coe_one] using hcone x

/-- The actual positive native pair coordinate gives the correctly ordered
closed corner cone. The two signs are actual coordinate facts, not a tiling
or angle-sum hypothesis. -/
theorem cofinite_native_ordered_corner_cone {p:ℍ} (R S:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt p)
    (hne:R.supportLine≠S.supportLine) (x q:ℍ) (hx:x∈R.val) (hxp:x≠p)
    (hq:q∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S) (s:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hsp:s • p=UpperHalfPlane.I) (t:ℝ) (ht:0<t)
    (hxt:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • x):ℂ)=(t:ℂ))
    (hqi:0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • q):ℂ).im) :
    ∀y:ℍ,y∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S) ↔
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)∈Submodule.span ℝ≥0
        {(1:ℂ),(Circle.exp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S):ℂ)} := by
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ s
  let R':=R.realGLMap g
  let S':=S.realGLMap g
  have hAux:∀(v:ℍ)(A B:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt v),v=UpperHalfPlane.I→
      A.supportLine≠B.supportLine→
      (s • x)∈A.val→s • x≠v→
      s • q∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior A B→
      ∀y:ℍ,y∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior A B) ↔
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y:ℂ)∈Submodule.span ℝ≥0
          {(1:ℂ),(Circle.exp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure A B):ℂ)}:=by
    intro v A B hv hn hAx hAxn hAq
    subst v
    have hu:=cofinite_centered_ray_unit A (s • x) hAx hAxn t ht hxt
    exact (cofinite_centered_corner_cone A B hn _ rfl hu (s • q) hAq hqi).2
  have hx':s • x∈R'.val:=by
    rw [←R.realGLMap_carrier]
    exact ⟨x,hx,rfl⟩
  have hq':s • q∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R' S':=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior_realGL_image R S hne g]
    exact ⟨q,hq,rfl⟩
  have hCone:=hAux (g • p) R' S' hsp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ray_support_ne_realGLMap R S hne g)
    hx' ((isometry_smul ℍ s).injective.ne hxp) hq'
  intro y
  have hy:y∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S) ↔
      s • y∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R' S'):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closure_properHAngleInterior_realGL_image R S hne g]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).injective.mem_set_image.symm
  rw [hy,hCone,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_realGLMap]


/-- The actual finite corner of the prescribed cofinite construction has a
positive native SL chart with its outgoing wall at angle zero and incoming
wall at the prescribed angle. Ideal neighboring endpoints remain allowed. -/
theorem cofiniteTangential_corner_chart {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) (z:𝔻)
    (hz:_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    let C:=((_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb).cornerTriangle i).finiteHalfPlaneCornerAtDiscA z hz
    ∃s:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z=UpperHalfPlane.I ∧
      ∀y:ℍ,y∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior C.rayAB C.rayAC) ↔
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (θ i):ℂ)} := by
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  let T:=S.cornerTriangle i
  let C:=T.finiteHalfPlaneCornerAtDiscA z hz
  let f:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)
  have hp:=cofiniteTangential_outgoing_orientation θ d hθ hd hb i z hz
  change 0<OriginalOrientation.signedArea
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate f) 0 at hp
  have hfne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z:=by
    intro he
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective he
    rw [hh] at hp
    exact (lt_irrefl (0:ℝ)) (by
      simpa only [OriginalOrientation.signedArea,sub_self,map_zero,zero_mul,Complex.zero_im] using hp)
  have hf:f∈{w:𝔻|_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w∈T.sideB}:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel f∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment T.c T.a
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_comm]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_foot_mem_edge θ d hθ hd hb i
  have hfR:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f∈C.rayAC.val:=by
    apply C.sideB_finite_subset (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]; exact hz)
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f))∈T.sideB
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  have hq:UpperHalfPlane.I∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior C.rayAC C.rayAB:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior_comm]
    exact cofiniteTangential_corner_origin θ d hθ hd hb i z hz
  obtain ⟨s,k,hk,hsp,hsf,hqi⟩:=cofiniteTangential_normalizer θ d hθ hd hb i z hz
  have ht:0<(k-1)/(k+1):=div_pos (by linarith only [hk]) (by linarith only [hk])
  have hsf':(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f):ℂ)=(((k-1)/(k+1):ℝ):ℂ):=by
    rw [hsf,cofinite_normalized_probe k hk]
  have hang:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure C.rayAC C.rayAB=θ i:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm]
    have he:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle θ d hθ hd hb i
    change S.toDiscPolygon.angle i=θ i at he
    rw [S.angle_eq_cornerTriangle,T.alpha_of_finite z hz,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane,T.cornerRayABAtA_toHalfPlane,
      T.cornerRayACAtA_toHalfPlane] at he
    exact he
  refine ⟨s,hsp,?_⟩
  have hqi':0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • UpperHalfPlane.I):ℂ).im:=by
    change 0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane 0):ℂ).im at hqi
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero] at hqi
  have hcone:=cofinite_native_ordered_corner_cone C.rayAC C.rayAB C.proper.symm
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f) UpperHalfPlane.I hfR hfne hq s hsp _ ht hsf' hqi'
  intro y
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior_comm,←hang]
  exact hcone y

/-- The full original tangential polygon carrier has its actual standard
closed-sector germ in the same positive native frame, with ideal neighbors
allowed. The carrier is not replaced by a model polygon. -/
theorem cofiniteTangential_corner_chart_germ {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) (z:𝔻)
    (hz:_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    ∃s:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z=UpperHalfPlane.I ∧
      ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z),
        y∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).carrier ↔
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (θ i):ℂ)} := by
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  let T:=S.cornerTriangle i
  let C:=T.finiteHalfPlaneCornerAtDiscA z hz
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  have hF:Tendsto _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)) (𝓝 z):=by
    have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_halfPlaneToDisc.tendsto (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] at h
  have hOpen:∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z),
      y∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).interior ↔y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior C.rayAB C.rayAC:=by
    have hm:=S.hasMinorInterior i z hz
    unfold _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.HasMinorInteriorAt at hm
    rw [S.cornerRayPrev_eq i z hz,S.cornerRayNext_eq i z hz,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior,T.cornerRayABAtA_toHalfPlane,T.cornerRayACAtA_toHalfPlane] at hm
    filter_upwards [hF.eventually hm] with y hy
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y∈Q.interior ↔_
    exact hy.trans _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.mem_set_image
  have hClosed:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hOpen
  obtain ⟨s,hs,hcone⟩:=cofiniteTangential_corner_chart θ d hθ hd hb i z hz
  refine ⟨s,hs,?_⟩
  filter_upwards [hClosed] with y hy
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier]
  exact hy.trans (hcone y)

/-- Every point on an actual centered forward ray has its actual positive
radial coordinate in the ray's unit direction. -/
theorem cofinite_centered_ray_coordinates (R:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt UpperHalfPlane.I)
    (x:ℍ) (hx:x∈R.val) (hxI:x≠UpperHalfPlane.I) :
    ∃r:ℝ,0<r ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:ℂ)=(r:ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection R:ℂ) := by
  have hx0:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:ℂ)≠0:=by
    intro he
    have hh:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x=0:=Complex.UnitDisc.coe_injective he
    have h:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane hh
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero] at h
    exact hxI h
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_I_cayley R R hx hxI R.directionPoint_mem.1 R.directionPoint_mem.2
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_self] at h
  obtain ⟨_,a,ha,he⟩:=angle_eq_zero_iff.mp h.symm
  have he':_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection R=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:ℂ),hx0⟩:=by
    change _root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc R.directionPoint:ℂ),triangleVertexTip_ne_zero R⟩=_
    have hsub:(⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc R.directionPoint:ℂ),triangleVertexTip_ne_zero R⟩:{w:ℂ//w≠0})=
        ⟨a • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:ℂ),smul_ne_zero ha.ne' hx0⟩:=Subtype.ext he
    rw [hsub,regular_direction_smul hx0 a ha]
  refine ⟨‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:ℂ)‖,norm_pos_iff.mpr hx0,?_⟩
  rw [he']
  exact (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection_reconstruct ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:ℂ),hx0⟩).symm

/-- Actual centered conformal rigidity turns positive marked ray coordinates
into the precise rotation. The radial scale equality follows from isometry. -/
theorem cofiniteSL_rotation_of_positive_rays (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:A • UpperHalfPlane.I=UpperHalfPlane.I) (z:𝔻)
    (t r:ℝ) (ht:0<t) (hr:0<r) (u:Circle)
    (hz:(z:ℂ)=(t:ℂ)) (hAz:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action A z:ℂ)=(r:ℂ)*(u:ℂ)) :
    ∀w:𝔻,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action A w=circleDiscRotationHom u w := by
  obtain ⟨a,b,hab,rfl⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_fix_I_rotation A hA
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL_disc_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation_coe,hz] at hAz
  have hn:=congrArg norm hAz
  rw [norm_mul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier_norm a b hab,one_mul,
    norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos ht,abs_of_pos hr] at hn
  have hcoef:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier a b=(u:ℂ):=by
    rw [←hn] at hAz
    apply mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne')
    simpa only [mul_comm] using hAz
  intro w
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL_disc_action]
  apply Complex.UnitDisc.coe_injective
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier a b*(w:ℂ)=(u:ℂ)*(w:ℂ)
  rw [hcoef]

/-- The same actual positive native frame carries every point of the two
original forward rays to its correctly ordered positive radial coordinate. -/
theorem cofinite_native_ordered_corner_ray_coordinates {p:ℍ} (R S:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt p)
    (hne:R.supportLine≠S.supportLine) (x q:ℍ) (hx:x∈R.val) (hxp:x≠p)
    (hq:q∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S) (s:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hsp:s • p=UpperHalfPlane.I) (t:ℝ) (ht:0<t)
    (hxt:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • x):ℂ)=(t:ℂ))
    (hqi:0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • q):ℂ).im) :
    (∀y:ℍ,y∈R.val→y≠p→∃r:ℝ,0<r ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)=(r:ℂ)) ∧
    (∀y:ℍ,y∈S.val→y≠p→∃r:ℝ,0<r ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)=
      (r:ℂ)*(Circle.exp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S):ℂ)) := by
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ s
  let R':=R.realGLMap g
  let S':=S.realGLMap g
  have hAux:∀(v:ℍ)(A B:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt v),v=UpperHalfPlane.I→
      A.supportLine≠B.supportLine→
      s • x∈A.val→s • x≠v→s • q∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior A B→
      (∀y:ℍ,y∈A.val→y≠v→∃r:ℝ,0<r ∧(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y:ℂ)=(r:ℂ)) ∧
      (∀y:ℍ,y∈B.val→y≠v→∃r:ℝ,0<r ∧(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y:ℂ)=
        (r:ℂ)*(Circle.exp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure A B):ℂ)):=by
    intro v A B hv hn hAx hAxn hAq
    subst v
    have hu:=cofinite_centered_ray_unit A (s • x) hAx hAxn t ht hxt
    have hv:_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexUnitDirection B=Circle.exp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure A B):=
      (cofinite_centered_corner_cone A B hn _ rfl hu (s • q) hAq hqi).1
    constructor
    · intro y hy hyn
      obtain ⟨r,hr,he⟩:=cofinite_centered_ray_coordinates A y hy hyn
      exact ⟨r,hr,by simpa only [hu,Circle.coe_one,mul_one] using he⟩
    · intro y hy hyn
      obtain ⟨r,hr,he⟩:=cofinite_centered_ray_coordinates B y hy hyn
      exact ⟨r,hr,by simpa only [hv] using he⟩
  have hx':s • x∈R'.val:=by
    rw [←R.realGLMap_carrier]
    exact ⟨x,hx,rfl⟩
  have hq':s • q∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R' S':=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior_realGL_image R S hne g]
    exact ⟨q,hq,rfl⟩
  obtain ⟨hR,hS⟩:=hAux (g • p) R' S' hsp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ray_support_ne_realGLMap R S hne g)
    hx' ((isometry_smul ℍ s).injective.ne hxp) hq'
  constructor
  · intro y hy hyn
    have hsy:s • y∈R'.val:=by
      rw [←R.realGLMap_carrier]
      exact ⟨y,hy,rfl⟩
    exact hR (s • y) hsy ((isometry_smul ℍ s).injective.ne hyn)
  · intro y hy hyn
    have hsy:s • y∈S'.val:=by
      rw [←S.realGLMap_carrier]
      exact ⟨y,hy,rfl⟩
    simpa only [R',S',_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_realGLMap] using
      hS (s • y) hsy ((isometry_smul ℍ s).injective.ne hyn)

/-- The actual cofinite polygon corner admits one and the same positive
SL frame for both original labelled rays and the whole closed corner cone. -/
theorem cofiniteTangential_frame_exists {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) (z:𝔻)
    (hz:_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    let C:=((_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb).cornerTriangle i).finiteHalfPlaneCornerAtDiscA z hz
    ∃s:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z=UpperHalfPlane.I ∧
      (∀y:ℍ,y∈C.rayAC.val→y≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z→
        ∃r:ℝ,0<r ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)=(r:ℂ)) ∧
      (∀y:ℍ,y∈C.rayAB.val→y≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z→
        ∃r:ℝ,0<r ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)=(r:ℂ)*(Circle.exp (θ i):ℂ)) ∧
      ∀y:ℍ,y∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior C.rayAB C.rayAC) ↔
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (θ i):ℂ)} := by
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  let T:=S.cornerTriangle i
  let C:=T.finiteHalfPlaneCornerAtDiscA z hz
  let f:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)
  have hp:=cofiniteTangential_outgoing_orientation θ d hθ hd hb i z hz
  change 0<OriginalOrientation.signedArea
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate f) 0 at hp
  have hfne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z:=by
    intro he
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective he
    rw [hh] at hp
    exact (lt_irrefl (0:ℝ)) (by
      simpa only [OriginalOrientation.signedArea,sub_self,map_zero,zero_mul,Complex.zero_im] using hp)
  have hf:f∈{w:𝔻|_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w∈T.sideB}:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel f∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment T.c T.a
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_comm]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_foot_mem_edge θ d hθ hd hb i
  have hfR:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f∈C.rayAC.val:=by
    apply C.sideB_finite_subset (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane];exact hz)
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f))∈T.sideB
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  have hq:UpperHalfPlane.I∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior C.rayAC C.rayAB:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior_comm]
    exact cofiniteTangential_corner_origin θ d hθ hd hb i z hz
  obtain ⟨s,k,hk,hsp,hsf,hqi⟩:=cofiniteTangential_normalizer θ d hθ hd hb i z hz
  have ht:0<(k-1)/(k+1):=div_pos (by linarith only [hk]) (by linarith only [hk])
  have hsf':(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f):ℂ)=(((k-1)/(k+1):ℝ):ℂ):=by
    rw [hsf,cofinite_normalized_probe k hk]
  have hqi':0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • UpperHalfPlane.I):ℂ).im:=by
    change 0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane 0):ℂ).im at hqi
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero] at hqi
  have hang:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure C.rayAC C.rayAB=θ i:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm]
    have he:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle θ d hθ hd hb i
    change S.toDiscPolygon.angle i=θ i at he
    rw [S.angle_eq_cornerTriangle,T.alpha_of_finite z hz,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane,T.cornerRayABAtA_toHalfPlane,
      T.cornerRayACAtA_toHalfPlane] at he
    exact he
  have hRays:=cofinite_native_ordered_corner_ray_coordinates C.rayAC C.rayAB C.proper.symm
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f) UpperHalfPlane.I hfR hfne hq s hsp _ ht hsf' hqi'
  have hCone:=cofinite_native_ordered_corner_cone C.rayAC C.rayAB C.proper.symm
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane f) UpperHalfPlane.I hfR hfne hq s hsp _ ht hsf' hqi'
  rw [hang] at hRays hCone
  refine ⟨s,hsp,hRays.1,hRays.2,?_⟩
  intro y
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior_comm]
  exact hCone y


open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The literal side-pairing map, with its actual finite and ideal extension. -/
def cofiniteTangentPairingClosedIsometry {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry where
  finiteMap z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (cofiniteTangentMirror θ d i j)
    (((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).geodesicSide i).reflection z)
  distance_eq z w := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap_pathDist]
    exact ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).geodesicSide i).closedReflectionIsometry.distance_eq z w
  closedMap := (((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).geodesicSide i).closedReflectionIsometry.closedMap).trans
    (cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j))
  finite_commutes z := by
    change cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)
      (((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).geodesicSide i).closedReflectionIsometry.closedMap
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z))=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes]
    rfl

theorem cofiniteTangentPairingClosedIsometry_finite {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n) (z:𝔻) :
    (cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j).finiteMap z=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (cofiniteTangentPairingElement θ d hθ hd hb i j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (cofiniteTangentMirror θ d i j)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i).reflection
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)))=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (cofiniteTangentMirror θ d i j)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i).reflection
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)))))
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]

/-- The original first closed endpoint maps to the paired side's last endpoint. -/
theorem cofiniteTangentPairingClosedIsometry_vertex_left {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) :
    (cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j).closedMap
      ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i)=
        (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices (finRotate n j) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  change cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)
    ((Q.geodesicSide i).closedReflectionIsometry.closedMap (Q.vertices i))=_
  rw [((Q.geodesicSide i).closedReflectionIsometry_fixed_iff (Q.vertices i)).mpr
    (Q.geodesicSide_endpoints i).1]
  exact cofiniteTangentMirror_vertex_left θ d hθ hd hb i j hl

/-- The other original endpoint maps to the paired side's first endpoint;
neither endpoint is required to be finite. -/
theorem cofiniteTangentPairingClosedIsometry_vertex_right {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hr:θ (finRotate n i)=θ j) :
    (cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j).closedMap
      ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices (finRotate n i))=
        (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices j := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  change cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)
    ((Q.geodesicSide i).closedReflectionIsometry.closedMap (Q.vertices (finRotate n i)))=_
  rw [((Q.geodesicSide i).closedReflectionIsometry_fixed_iff (Q.vertices (finRotate n i))).mpr
    (Q.geodesicSide_endpoints i).2]
  exact cofiniteTangentMirror_vertex_right θ d hθ hd hb i j hr

/-- The actual finite current vertex has an actual finite successor under
the side-pairing map, with no finiteness assumption on adjacent vertices. -/
theorem cofiniteTangentPairingElement_vertex {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (z:𝔻)
    (hz:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices (finRotate n j)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
        (cofiniteTangentPairingElement θ d hθ hd hb i j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))) := by
  have he:=cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i j hl
  rw [hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes,cofiniteTangentPairingClosedIsometry_finite] at he
  exact he.symm

theorem cofiniteTangentPairingElement_vertex_eq {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (z w:𝔻)
    (hz:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hw:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices (finRotate n j)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w) :
    cofiniteTangentPairingElement θ d hθ hd hb i j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w := by
  have he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (cofiniteTangentPairingElement θ d hθ hd hb i j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))=w :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective
      ((cofiniteTangentPairingElement_vertex θ d hθ hd hb i j hl z hz).symm.trans hw)
  have hh:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane he
  rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] at hh

/-- The actual compactified side is transported with its ordered endpoints,
also when the neighboring endpoint is ideal. -/
theorem cofiniteTangentPairingClosedIsometry_segment {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j) :
    (cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j).closedMap ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment
        ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i)
        ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices (finRotate n i))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment
        ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices (finRotate n j))
        ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices j) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.image_closedModelDiscHSegment,
    cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i j hl,
    cofiniteTangentPairingClosedIsometry_vertex_right θ d hθ hd hb i j hr]

/-- The full genuine forward ray toward a finite or ideal endpoint is
transported by a genuine compactified native isometry. -/
theorem cofinite_discRayTowardClosed_map (e:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry) (z:𝔻) (q:𝕔𝔻)
    (hzq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠q) :
    (_root_.LowDimensionalTopology.Geometry.Polygon.discRayTowardClosed z q hzq).mapClosedIsometry e=
      _root_.LowDimensionalTopology.Geometry.Polygon.discRayTowardClosed (e.finiteMap z) (e.closedMap q)
        (by rw [←e.finite_commutes];exact e.closedMap.injective.ne hzq) := by
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDisc_interior_or_ideal q with ⟨w,rfl⟩|hq
  · have hzw:z≠w:=fun he=>hzq (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel he)
    have hn:e.finiteMap z≠e.finiteMap w:=e.finiteMap_bijective.1.ne hzw
    simp only [e.finite_commutes]
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.discRayTowardClosed_finite _ _ hn]
    symm
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough_eq hn
    refine ⟨w,?_,rfl⟩
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.discRayTowardClosed_finite z w hzw]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRayThrough_mem z w hzw
  · apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.eq_of_idealEndpoint_eq
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.mapClosedIsometry_idealEndpoint _ e q hq
        (_root_.LowDimensionalTopology.Geometry.Polygon.discRayTowardClosed_idealEndpoint z q hzq hq),
      _root_.LowDimensionalTopology.Geometry.Polygon.discRayTowardClosed_idealEndpoint _ _ _ ((e.ideal_iff q).mpr hq)]

/-- The literal outgoing side ray maps to the literal incoming side ray at
the actual successor vertex. The adjacent endpoints may be ideal. -/
theorem cofiniteTangentPairingClosedIsometry_cornerRay {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j)
    (z:𝔻) (hz:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let e:=cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j
    e.finiteMap '' (Q.cornerRayNext i z hz).val=
      (Q.cornerRayPrev (finRotate n j) (e.finiteMap z)
        (by rw [←e.finite_commutes,←hz];exact
          (cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i j hl).symm)).val := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let e:=cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j
  have hn:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠Q.vertices (finRotate n i):=by
    rw [←hz]
    exact Q.vertices_injective.ne (Q.next_ne_self i).symm
  have hr':e.closedMap (Q.vertices (finRotate n i))=Q.vertices j:=
    cofiniteTangentPairingClosedIsometry_vertex_right θ d hθ hd hb i j hr
  have hmap:=congrArg (fun R:_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt (e.finiteMap z)=>R.val)
    (cofinite_discRayTowardClosed_map e z (Q.vertices (finRotate n i)) hn)
  simpa only [_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.cornerRayNext,_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.cornerRayPrev,
    Equiv.symm_apply_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.mapClosedIsometry_carrier,hr'] using hmap


theorem cofiniteTangentPairingClosedIsometry_native {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n) (z:𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane ((cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j).finiteMap z)=
      cofiniteTangentPairingElement θ d hθ hd hb i j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) := by
  rw [cofiniteTangentPairingClosedIsometry_finite,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]

/-- Transport of the entire genuine native forward carrier, with its direction
and actual successor point retained. -/
theorem cofiniteTangentPairingElement_native_cornerRay {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j)
    (z:𝔻) (hz:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let e:=cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j
    cofiniteTangentPairingElement θ d hθ hd hb i j '' (Q.cornerRayNext i z hz).toHalfPlane.val=
      (Q.cornerRayPrev (finRotate n j) (e.finiteMap z)
        (by rw [←e.finite_commutes,←hz];exact
          (cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i j hl).symm)).toHalfPlane.val := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let e:=cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j
  have hRay:=cofiniteTangentPairingClosedIsometry_cornerRay θ d hθ hd hb i j hl hr z hz
  change cofiniteTangentPairingElement θ d hθ hd hb i j ''
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' (Q.cornerRayNext i z hz).val)=_
  calc
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' (e.finiteMap '' (Q.cornerRayNext i z hz).val) := by
      rw [image_image,image_image]
      congr 1
    _=_:=by rw [hRay];rfl

/-- Inverse matching supplies the second endpoint condition automatically
for the actual involutive side labels. -/
theorem cofiniteTangentialPairing_other_angle {n:ℕ} (θ:Fin n→ℝ)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) :
    θ (finRotate n i)=θ (ρ i) := by
  simpa only [hρ i] using (hθρ (ρ i)).symm


/-- The actual labelled side pairing carries each finite current corner to
its literal natural successor, with that successor's finiteness derived. -/
theorem cofiniteTangentialSidePairing_vertex_transport {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (ρ:Equiv.Perm (Fin n))
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n)
    (z:𝔻) (hz:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices (finRotate n (ρ i))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
        (cofiniteTangentPairingElement θ d hθ hd hb i (ρ i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))) :=
  cofiniteTangentPairingElement_vertex θ d hθ hd hb i (ρ i) (hθρ i) z hz

/-- All literal outgoing native rays are carried to the incoming native rays
at their actual natural successors for the same involutive side pairing. -/
theorem cofiniteTangentialSidePairing_ray_transport {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (ρ:Equiv.Perm (Fin n))
    (hρ:Function.Involutive ρ) (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n)
    (z:𝔻) (hz:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let e:=cofiniteTangentPairingClosedIsometry θ d hθ hd hb i (ρ i)
    cofiniteTangentPairingElement θ d hθ hd hb i (ρ i) '' (Q.cornerRayNext i z hz).toHalfPlane.val=
      (Q.cornerRayPrev (finRotate n (ρ i)) (e.finiteMap z)
        (by rw [←e.finite_commutes,←hz];exact
          (cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i (ρ i) (hθρ i)).symm)).toHalfPlane.val :=
  cofiniteTangentPairingElement_native_cornerRay θ d hθ hd hb i (ρ i)
    (hθρ i) (cofiniteTangentialPairing_other_angle θ ρ hρ hθρ i) z hz


/-- The actual pairing, expressed in its two actual positive corner frames,
is precisely the rotation through the original target corner angle. -/
theorem cofiniteTangentPairing_frame_rotation {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j)
    (z:𝔻) (hz:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let e:=cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j
    let w:=e.finiteMap z
    let hw:Q.vertices (finRotate n j)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w:=by
      rw [←e.finite_commutes,←hz]
      exact (cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i j hl).symm
    ∀si sj:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      si • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z=UpperHalfPlane.I→
      sj • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w=UpperHalfPlane.I→
      (∀x:ℍ,x∈(Q.cornerRayNext i z hz).toHalfPlane.val→x≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z→
        ∃r:ℝ,0<r ∧(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (si • x):ℂ)=(r:ℂ))→
      (∀x:ℍ,x∈(Q.cornerRayPrev (finRotate n j) w hw).toHalfPlane.val→x≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w→
        ∃r:ℝ,0<r ∧(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (sj • x):ℂ)=(r:ℂ)*(Circle.exp (θ i):ℂ))→
      ∀y:ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (sj •
        (cofiniteTangentPairingElement θ d hθ hd hb i j (si⁻¹ • y)))=
        circleDiscRotationHom (Circle.exp (θ i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let e:=cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j
  let w:=e.finiteMap z
  have hw:Q.vertices (finRotate n j)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w:=by
    rw [←e.finite_commutes,←hz]
    exact (cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i j hl).symm
  dsimp only
  intro si sj hsi hsj hi hj
  let A:=cofiniteTangentPairingElement θ d hθ hd hb i j
  let R:=(Q.cornerRayNext i z hz).toHalfPlane
  let x:=R.directionPoint
  have hx:x∈R.val:=R.directionPoint_mem.1
  have hxp:x≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z:=R.directionPoint_mem.2
  have hAp:A (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w:=
    cofiniteTangentPairingElement_vertex_eq θ d hθ hd hb i j hl z w hz hw
  have hAx:A x∈(Q.cornerRayPrev (finRotate n j) w hw).toHalfPlane.val:=by
    rw [←cofiniteTangentPairingElement_native_cornerRay θ d hθ hd hb i j hl hr z hz]
    exact ⟨x,hx,rfl⟩
  have hAxp:A x≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w:=by
    rw [←hAp]
    exact A.injective.ne hxp
  obtain ⟨ri,hri,hRi⟩:=hi x hx hxp
  obtain ⟨rj,hrj,hRj⟩:=hj (A x) hAx hAxp
  obtain ⟨a,ha⟩:=cofiniteTangentPairingElement_conformal θ d hθ hd hb i j
  have ha':∀v:ℍ,a • v=A v:=fun v=>congrArg (fun f:ℍ≃ᵢℍ=>f v) ha
  let B:=sj*a*si⁻¹
  have hBi:B • UpperHalfPlane.I=UpperHalfPlane.I:=by
    change (sj*a*si⁻¹) • UpperHalfPlane.I=UpperHalfPlane.I
    have hinv:si⁻¹ • UpperHalfPlane.I=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z:=by
      rw [←hsi,inv_smul_smul]
    rw [mul_smul,mul_smul,hinv,ha',hAp,hsj]
  let zx:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (si • x)
  have hBz:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action B zx:ℂ)=(rj:ℂ)*(Circle.exp (θ i):ℂ):=by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ((sj*a*si⁻¹) • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (si • x))):ℂ)=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,mul_smul,mul_smul,inv_smul_smul,ha']
    exact hRj
  have hRot:=cofiniteSL_rotation_of_positive_rays B hBi zx ri rj hri hrj (Circle.exp (θ i)) hRi hBz
  intro y
  have h:=hRot (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y)
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ((sj*a*si⁻¹) • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y))=_ at h
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,mul_smul,mul_smul,ha'] at h
  exact h

/-- One actual positive coordinate simultaneously normalizes the two
labelled rays and the literal polygon carrier germ. -/
theorem cofiniteTangential_polygon_frame_exists {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) (z:𝔻)
    (hz:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    ∃s:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z=UpperHalfPlane.I ∧
      (∀y:ℍ,y∈(Q.cornerRayNext i z hz).toHalfPlane.val→y≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z→
        ∃r:ℝ,0<r ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)=(r:ℂ)) ∧
      (∀y:ℍ,y∈(Q.cornerRayPrev i z hz).toHalfPlane.val→y≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z→
        ∃r:ℝ,0<r ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)=(r:ℂ)*(Circle.exp (θ i):ℂ)) ∧
      ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z),y∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier ↔
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (θ i):ℂ)} := by
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  let T:=S.cornerTriangle i
  let C:=T.finiteHalfPlaneCornerAtDiscA z hz
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  obtain ⟨s,hs,hOut,hIn,hCone⟩:=cofiniteTangential_frame_exists θ d hθ hd hb i z hz
  refine ⟨s,hs,?_,?_,?_⟩
  · intro y hy hyn
    have hy':y∈C.rayAC.val:=by
      change y∈(S.toDiscPolygon.cornerRayNext i z hz).toHalfPlane.val at hy
      rw [S.cornerRayNext_eq i z hz,T.cornerRayACAtA_toHalfPlane] at hy
      exact hy
    exact hOut y hy' hyn
  · intro y hy hyn
    have hy':y∈C.rayAB.val:=by
      change y∈(S.toDiscPolygon.cornerRayPrev i z hz).toHalfPlane.val at hy
      rw [S.cornerRayPrev_eq i z hz,T.cornerRayABAtA_toHalfPlane] at hy
      exact hy
    exact hIn y hy' hyn
  · have hF:Tendsto _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)) (𝓝 z):=by
      have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_halfPlaneToDisc.tendsto (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)
      rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] at h
    have hOpen:∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z),
        y∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).interior ↔y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior C.rayAB C.rayAC:=by
      have hm:=S.hasMinorInterior i z hz
      unfold _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.HasMinorInteriorAt at hm
      rw [S.cornerRayPrev_eq i z hz,S.cornerRayNext_eq i z hz,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior,T.cornerRayABAtA_toHalfPlane,T.cornerRayACAtA_toHalfPlane] at hm
      filter_upwards [hF.eventually hm] with y hy
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y∈Q.interior ↔_
      exact hy.trans _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.mem_set_image
    filter_upwards [_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hOpen] with y hy
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier]
    exact hy.trans (hCone y)

/-- Actual finite tangential polygons carry a simultaneous family of
positive frames, with every genuine side crossing equal to the prescribed
rotation. All frame and crossing identities are conclusions. -/
theorem cofiniteTangential_finite_frames {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (ρ:Equiv.Perm (Fin n))
    (hρ:Function.Involutive ρ) (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    ∃(z:Fin n→𝔻)(F:Fin n→Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀i,Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (z i)) ∧
      (∀i,F i • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z i)=UpperHalfPlane.I) ∧
      (∀i,∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z i)),y∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier ↔
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • y):ℂ)∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (θ i):ℂ)}) ∧
      ∀i:Fin n,∀y:ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F (finRotate n (ρ i)) •
        (cofiniteTangentPairingElement θ d hθ hd hb i (ρ i) ((F i)⁻¹ • y)))=
        circleDiscRotationHom (Circle.exp (θ i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let z:Fin n→𝔻:=fun i=>Complex.UnitDisc.mk (Q.vertices i:ℂ) (hf i)
  have hz:∀i,Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (z i):=fun _=>Subtype.ext rfl
  have hFex:=fun i=>cofiniteTangential_polygon_frame_exists θ d hθ hd hb i (z i) (hz i)
  choose F hF using hFex
  refine ⟨z,F,hz,fun i=>(hF i).1,fun i=>(hF i).2.2.2,?_⟩
  intro i y
  let j:=ρ i
  let k:=finRotate n j
  let e:=cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j
  let w:=e.finiteMap (z i)
  have hw:Q.vertices k=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w:=by
    rw [←e.finite_commutes,←hz i]
    exact (cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i j (hθρ i)).symm
  have hwz:w=z k:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective (hw.symm.trans (hz k))
  have hrot:=cofiniteTangentPairing_frame_rotation θ d hθ hd hb i j (hθρ i)
    (cofiniteTangentialPairing_other_angle θ ρ hρ hθρ i) (z i) (hz i)
  dsimp only at hrot
  apply hrot (F i) (F k) (hF i).1
  · change F k • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w=UpperHalfPlane.I
    rw [hwz]
    exact (hF k).1
  · exact (hF i).2.1
  · intro x hx hxp
    change x∈(Q.cornerRayPrev k w hw).toHalfPlane.val at hx
    have hMove:∀(v:𝔻)(hv:Q.vertices k=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel v),v=z k→
        (Q.cornerRayPrev k v hv).toHalfPlane.val=(Q.cornerRayPrev k (z k) (hz k)).toHalfPlane.val:=by
      intro v hv he
      subst v
      rfl
    have hx':x∈(Q.cornerRayPrev k (z k) (hz k)).toHalfPlane.val:=by
      rw [hMove w hw hwz] at hx
      exact hx
    have hxp':x≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z k):=by
      change x≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w at hxp
      rwa [hwz] at hxp
    obtain ⟨r,hr,he⟩:=(hF k).2.2.1 x hx' hxp'
    refine ⟨r,hr,?_⟩
    rw [←hθρ i] at he
    exact he

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces

/-- The literal successive inverse-side word in the genuine native isometry
group. No discreteness or presentation relation is built into this word. -/
def nativeAngularWalkWord (A:ℕ→(ℍ≃ᵢℍ)) : ℕ→(ℍ≃ᵢℍ)
  | 0=>1
  | j+1=>nativeAngularWalkWord A j*(A j)⁻¹

/-- Actual positive native frame transitions add their rotation angles along
the literal side word. Both constant and unequal corner angles are allowed. -/
theorem nativeAngularWalk_coordinate (A:ℕ→(ℍ≃ᵢℍ))
    (F:ℕ→Matrix.SpecialLinearGroup (Fin 2) ℝ) (β:ℕ→ℝ)
    (hStep:∀j:ℕ,∀x:ℍ,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F (j+1) • A j x):ℂ)=
      (Circle.exp (β j):ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F j • x):ℂ)) :
    ∀j:ℕ,∀x:ℍ,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F 0 • nativeAngularWalkWord A j x):ℂ)=
      (Circle.exp (-(∑k∈Finset.range j,β k)):ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F j • x):ℂ) := by
  intro j
  induction j with
  | zero =>
    intro x
    simp only [nativeAngularWalkWord,Finset.range_zero,Finset.sum_empty,
      neg_zero,Circle.exp_zero,Circle.coe_one,one_mul]
    rfl
  | succ j ih =>
    intro x
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F 0 • nativeAngularWalkWord A j ((A j)⁻¹ x)):ℂ)=_
    rw [ih]
    have hs:=hStep j ((A j)⁻¹ x)
    have hAx:A j ((A j)⁻¹ x)=x:=(A j).apply_symm_apply x
    rw [hAx] at hs
    have hb:=congrArg (fun z:ℂ=>(Circle.exp (-(β j)):ℂ)*z) hs
    rw [←mul_assoc,←Circle.coe_mul,←Circle.exp_add,neg_add_cancel,Circle.exp_zero,
      Circle.coe_one,one_mul] at hb
    rw [←hb,←mul_assoc,←Circle.coe_mul,←Circle.exp_add,Finset.sum_range_succ]
    rw [show -(∑k∈Finset.range j,β k)+ -(β j)=
      -((∑k∈Finset.range j,β k)+β j) by ring]

/-- A complete actual frame cycle with one full integral angular turn has
identity native word; no faithfulness or desired group relation is assumed. -/
theorem nativeAngularWalk_word_eq_one (A:ℕ→(ℍ≃ᵢℍ))
    (F:ℕ→Matrix.SpecialLinearGroup (Fin 2) ℝ) (β:ℕ→ℝ)
    (hStep:∀j:ℕ,∀x:ℍ,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F (j+1) • A j x):ℂ)=
      (Circle.exp (β j):ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F j • x):ℂ))
    (N:ℕ) (hFrame:F N=F 0) (hTurn:Circle.exp (∑k∈Finset.range N,β k)=1) :
    nativeAngularWalkWord A N=1 := by
  have hi:Circle.exp (-(∑k∈Finset.range N,β k))=1:=by
    rw [Circle.exp_neg,hTurn,inv_one]
  apply IsometryEquiv.ext
  intro x
  change nativeAngularWalkWord A N x=x
  apply (isometry_smul ℍ (F 0)).injective
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
  apply Complex.UnitDisc.coe_injective
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F 0 • nativeAngularWalkWord A N x):ℂ)=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F 0 • x):ℂ)
  simpa only [hFrame,hi,Circle.coe_one,one_mul] using nativeAngularWalk_coordinate A F β hStep N x

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The actual reversed-endpoint pairing preserves the literal corner angle
along every actual natural label orbit. -/
theorem cofiniteTangential_angle_iterate {n:ℕ} (θ:Fin n→ℝ)
    (ρ:Equiv.Perm (Fin n)) (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (j:ℕ) :
    θ (((ρ.trans (finRotate n))^[j]) i)=θ i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (hθρ _).symm.trans ih

/-- The complete actual angular label period gives identity for the literal
native inverse-side word. The frame system is constructed internally from
the true polygon; no holonomy relation or developing-map hypothesis is added. -/
theorem cofiniteTangential_finite_word_period {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (ρ:Equiv.Perm (Fin n))
    (hρ:Function.Involutive ρ) (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (i:Fin n) (N:ℕ) (hN:0<N)
    (hCycle:((ρ.trans (finRotate n))^[N]) i=i)
    (hAngle:θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) :
    nativeAngularWalkWord (fun j=>cofiniteTangentPairingElement θ d hθ hd hb
      (((ρ.trans (finRotate n))^[j]) i) (ρ (((ρ.trans (finRotate n))^[j]) i))) N=1 := by
  let τ:=ρ.trans (finRotate n)
  obtain ⟨z,F,_hz,_hcenter,_hgerm,hFrame⟩:=cofiniteTangential_finite_frames θ d hθ hd hb ρ hρ hθρ hf
  let A:ℕ→(ℍ≃ᵢℍ):=fun j=>cofiniteTangentPairingElement θ d hθ hd hb (τ^[j] i) (ρ (τ^[j] i))
  let G:ℕ→Matrix.SpecialLinearGroup (Fin 2) ℝ:=fun j=>F (τ^[j] i)
  let β:ℕ→ℝ:=fun j=>θ (τ^[j] i)
  have hStep:∀j:ℕ,∀x:ℍ,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G (j+1) • A j x):ℂ)=
      (Circle.exp (β j):ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G j • x):ℂ):=by
    intro j x
    have h:=hFrame (τ^[j] i) (F (τ^[j] i) • x)
    rw [inv_smul_smul] at h
    have hh:=congrArg (fun w:𝔻=>(w:ℂ)) h
    rw [circleDiscRotationHom_apply] at hh
    simpa only [G,A,β,Function.iterate_succ_apply',τ,Equiv.trans_apply] using hh
  have hGF:G N=G 0:=by
    dsimp only [G]
    rw [hCycle]
    rfl
  have hsum:(∑k∈Finset.range N,β k)=2*Real.pi:=by
    calc
      (∑k∈Finset.range N,β k)=∑_k∈Finset.range N,θ i:=by
        apply Finset.sum_congr rfl
        intro k _hk
        exact cofiniteTangential_angle_iterate θ ρ hθρ i k
      _=(N:ℝ)*θ i:=by simp
      _=2*Real.pi:=by rw [hAngle];exact _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod_mul N hN.ne'
  have hTurn:Circle.exp (∑k∈Finset.range N,β k)=1:=by
    rw [hsum,Circle.exp_two_pi]
  exact nativeAngularWalk_word_eq_one A G β hStep N hGF hTurn

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
local instance closedAngleFanDiscMetric : MetricSpace 𝔻:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric

/-- Actual equal-angle closed germs cover a true native ball. Arbitrary open
subsets of those actual closed pieces are disjoint there, without an assumed
description of their open sector germs. -/
theorem native_closed_angle_germs_ball_fan (n:ℕ) (hn:0<n) (u:Circle)
    (hu:orderOf u=n) (p:ℍ) (e:ℍ≃ᵢ𝔻) (C O:Fin n→Set ℍ)
    (hgerm:∀i:Fin n,∀ᶠx in 𝓝 p,
      x∈C i ↔e x∈circleDiscRotationHom (u^i.val) ''
        {z:𝔻|(z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector n})
    (hO:∀i,IsOpen (O i)) (hOC:∀i,O i⊆C i) :
    ∃r:ℝ,0<r ∧∀s:ℝ,0<s→s≤r→
      (⋃i:Fin n,C i∩Metric.ball p s)=Metric.ball p s ∧
      Pairwise (fun i j:Fin n=>Disjoint (O i∩Metric.ball p s) (O j∩Metric.ball p s)) := by
  let U:Fin n→Set 𝔻:=fun i=>circleDiscRotationHom (u^i.val) ''
    {z:𝔻|(z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n}
  let V:Fin n→Set 𝔻:=fun i=>circleDiscRotationHom (u^i.val) ''
    {z:𝔻|(z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector n}
  have hbase:closure {z:𝔻|(z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n}=
      {z:𝔻|(z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector n}:=by
    have hco:IsOpenMap ((↑):𝔻→ℂ):=by
      change IsOpenMap ((↑):Metric.ball (0:ℂ) 1→ℂ)
      exact Metric.isOpen_ball.isOpenMap_subtype_val
    have hc:=hco.preimage_closure_eq_closure_preimage
      Complex.UnitDisc.continuous_coe (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n)
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector_closure n hn] at hc
    exact hc.symm
  have hU:∀i,IsOpen (U i):=by
    intro i
    exact (circleDiscRotationHom (u^i.val)).toHomeomorph.isOpenMap _
      ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector_isOpen n).preimage Complex.UnitDisc.continuous_coe)
  have hcl:∀i,closure (U i)=V i:=by
    intro i
    have hc:=(circleDiscRotationHom (u^i.val)).toHomeomorph.image_closure
      {z:𝔻|(z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n}
    rw [hbase] at hc
    exact hc.symm
  have hDis:Pairwise (fun i j:Fin n=>Disjoint (interior (V i)) (interior (V j))):=by
    intro i j hij
    have hd:Disjoint (U i) (U j):=regular_circle_open_sector_disjoint u n hn hu hij
    have hi:Disjoint (interior (closure (U i))) (U j):=
      (hd.closure_left (hU j)).mono_left interior_subset
    have hj:Disjoint (interior (closure (U i))) (interior (closure (U j))):=
      (hi.closure_right isOpen_interior).mono_right interior_subset
    simpa only [hcl] using hj
  have hg:∀ᶠx in 𝓝 p,∀i:Fin n,x∈C i ↔e x∈V i:=eventually_all.mpr hgerm
  obtain ⟨r,hr,hball⟩:=Metric.eventually_nhds_iff.mp hg
  refine ⟨r,hr,?_⟩
  intro s _hs hsr
  have hG (x:ℍ) (hx:x∈Metric.ball p s):=hball (lt_of_lt_of_le hx hsr)
  constructor
  · ext x
    constructor
    · intro hx
      obtain ⟨i,hxi⟩:=mem_iUnion.mp hx
      exact hxi.2
    · intro hx
      obtain ⟨i,z,hz,hzx⟩:=regular_circle_closed_sector_cover u n hn hu (e x)
      exact mem_iUnion.mpr ⟨i,(hG x hx i).mpr ⟨z,hz,hzx⟩,hx⟩
  · have hImage:∀i,e '' (O i∩Metric.ball p s)⊆interior (V i):=by
      intro i
      apply interior_maximal
      · rintro _ ⟨x,hx,rfl⟩
        exact (hG x hx.2 i).mp (hOC i hx.1)
      · exact e.toHomeomorph.isOpenMap _ ((hO i).inter Metric.isOpen_ball)
    intro i j hij
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp (hDis hij)
      (hImage i (mem_image_of_mem e hx)) (hImage j (mem_image_of_mem e hy))


end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
local instance tangentialFanDiscMetric : MetricSpace 𝔻:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric

/-- The literal inverse-side word tiles a genuine ball at the original finite
corner, using the actual internally constructed positive frames. -/
theorem cofiniteTangential_finite_cycle_ball_fan {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (ρ:Equiv.Perm (Fin n))
    (hρ:Function.Involutive ρ) (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (i:Fin n) (w:𝔻)
    (hw:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w)
    (N:ℕ) (hN:3≤N) (hAngle:θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) :
    let τ:=ρ.trans (finRotate n)
    let A:ℕ→(ℍ≃ᵢℍ):=fun j=>cofiniteTangentPairingElement θ d hθ hd hb (τ^[j] i) (ρ (τ^[j] i))
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)
    ∃r:ℝ,0<r ∧∀s:ℝ,0<s→s≤r→
      (⋃j:Fin N,(nativeAngularWalkWord A j.val '' P.carrier)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) s)=
        Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) s ∧
      Pairwise (fun j k:Fin N=>Disjoint
        ((nativeAngularWalkWord A j.val '' P.interior)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) s)
        ((nativeAngularWalkWord A k.val '' P.interior)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) s)) := by
  let τ:=ρ.trans (finRotate n)
  let A:ℕ→(ℍ≃ᵢℍ):=fun j=>cofiniteTangentPairingElement θ d hθ hd hb (τ^[j] i) (ρ (τ^[j] i))
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)
  obtain ⟨z,F,hz,hcenter,hgerm,hFrame⟩:=cofiniteTangential_finite_frames θ d hθ hd hb ρ hρ hθρ hf
  have hzi:z i=w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective ((hz i).symm.trans hw)
  let G:ℕ→Matrix.SpecialLinearGroup (Fin 2) ℝ:=fun j=>F (τ^[j] i)
  let β:ℕ→ℝ:=fun j=>θ (τ^[j] i)
  have hStep:∀j:ℕ,∀x:ℍ,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G (j+1) • A j x):ℂ)=
      (Circle.exp (β j):ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G j • x):ℂ):=by
    intro j x
    have h:=hFrame (τ^[j] i) (F (τ^[j] i) • x)
    rw [inv_smul_smul] at h
    have hh:=congrArg (fun q:𝔻=>(q:ℂ)) h
    rw [circleDiscRotationHom_apply] at hh
    simpa only [G,A,β,Function.iterate_succ_apply',τ,Equiv.trans_apply] using hh
  let u:Circle:=(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator N)⁻¹
  have hu:orderOf u=N:=by
    change orderOf ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator N)⁻¹)=N
    rw [orderOf_inv]
    exact (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot N (by omega)).eq_orderOf.symm
  have hphase (j:ℕ):Circle.exp (-(∑k∈Finset.range j,β k))=u^j:=by
    have hsum:(∑k∈Finset.range j,β k)=(j:ℝ)*θ i:=by
      calc
        _=∑_k∈Finset.range j,θ i:=by
          apply Finset.sum_congr rfl
          intro k _hk
          exact cofiniteTangential_angle_iterate θ ρ hθρ i k
        _=_:=by simp
    rw [hsum,hAngle,neg_mul_eq_mul_neg,Circle.exp_natCast_mul,Circle.exp_neg]
    rfl
  have hcoord (j:ℕ) (x:ℍ):
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • nativeAngularWalkWord A j x)=
        circleDiscRotationHom (u^j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G j • x)):=by
    apply Complex.UnitDisc.coe_injective
    have hh:=nativeAngularWalk_coordinate A G β hStep j x
    simpa only [G,Function.iterate_zero,Function.id_def,hphase,circleDiscRotationHom_apply] using hh
  have hWordCenter (j:ℕ):nativeAngularWalkWord A j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j] i)))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w:=by
    apply (isometry_smul ℍ (F i)).injective
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • nativeAngularWalkWord A j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j] i))))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)
    rw [hcoord]
    dsimp only [G]
    rw [hcenter]
    have hci:F i • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w=UpperHalfPlane.I:=by simpa only [hzi] using hcenter i
    rw [hci]
    have h0:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=0:=by
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    rw [h0]
    apply Complex.UnitDisc.coe_injective
    change ((u^j:Circle):ℂ)*(0:ℂ)=0
    exact mul_zero _
  let e:ℍ≃ᵢ𝔻:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F i)).trans triangleVertexCayleyIsometry
  let C:Fin N→Set ℍ:=fun j=>nativeAngularWalkWord A j.val '' P.carrier
  let O:Fin N→Set ℍ:=fun j=>nativeAngularWalkWord A j.val '' P.interior
  have hGerm:∀j:Fin N,∀ᶠx in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w),
      x∈C j ↔e x∈circleDiscRotationHom (u^j.val) ''
        {q:𝔻|(q:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector N}:=by
    intro j
    have hcont:Continuous (((nativeAngularWalkWord A j.val).symm):ℍ→ℍ):=
      ((nativeAngularWalkWord A j.val).symm).continuous
    have hpre:((nativeAngularWalkWord A j.val).symm) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j.val] i)):=by
      rw [←hWordCenter j.val]
      exact (nativeAngularWalkWord A j.val).symm_apply_apply _
    have ht:Tendsto (((nativeAngularWalkWord A j.val).symm):ℍ→ℍ)
        (𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)) (𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j.val] i)))):=by
      simpa only [hpre] using hcont.tendsto (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)
    filter_upwards [ht.eventually (hgerm (τ^[j.val] i))] with x hx
    have hin:x∈C j ↔((nativeAngularWalkWord A j.val).symm x)∈P.carrier:=by
      constructor
      · rintro ⟨y,hy,rfl⟩
        simpa only [(nativeAngularWalkWord A j.val).symm_apply_apply] using hy
      · intro hy
        exact ⟨_,hy,(nativeAngularWalkWord A j.val).apply_symm_apply x⟩
    rw [hin,hx,cofiniteTangential_angle_iterate θ ρ hθρ i j.val,hAngle]
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G j.val • (nativeAngularWalkWord A j.val).symm x):ℂ)∈
      (Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N):ℂ)}:Set ℂ)) ↔_
    rw [←_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector_eq_span N hN]
    have he:e x=circleDiscRotationHom (u^j.val)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G j.val • ((nativeAngularWalkWord A j.val).symm x))):=by
      have hh:=hcoord j.val (((nativeAngularWalkWord A j.val).symm) x)
      rw [(nativeAngularWalkWord A j.val).apply_symm_apply] at hh
      exact hh
    rw [he]
    constructor
    · intro hy
      exact mem_image_of_mem (circleDiscRotationHom (u^j.val)) hy
    · rintro ⟨q,hq,hqeq⟩
      exact (circleDiscRotationHom (u^j.val)).injective hqeq ▸ hq
  have hOpen:∀j,IsOpen (O j):=by
    intro j
    exact (nativeAngularWalkWord A j.val).toHomeomorph.isOpenMap _ (by exact _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_interior_isOpen _)
  have hOC:∀j,O j⊆C j:=by
    intro j
    exact Set.image_mono P.interior_subset_carrier
  exact native_closed_angle_germs_ball_fan N (by omega) u hu (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) e C O hGerm hOpen hOC

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The unchanged actual pairing, with the definitionally equal finite polygon type explicit. -/
def cofiniteTangentialFiniteSidePairing {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) :
    _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf) :=
  cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ

def cofiniteTangentialCanonicalIndex {n:ℕ} (ρ:Equiv.Perm (Fin n)) : Equiv.Perm (Fin n):=
  ρ.trans (finRotate n)

/-- The same original side labels are retained by the all-finite specialization. -/
theorem cofiniteTangentialSideEquiv_finite {n:ℕ} (Q:_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hf:∀i,‖(Q.vertices i:ℂ)‖<1) :
    _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf := rfl

theorem cofiniteTangentialSidePairing_element_index {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) :
    (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).element
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i)=
        cofiniteTangentPairingElement θ d hθ hd hb i (ρ i) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  change cofiniteTangentPairingElement θ d hθ hd hb
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).symm (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i))
    (ρ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).symm (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i)))=_
  rw [Equiv.symm_apply_apply]

theorem cofiniteTangentialSidePairing_paired_index {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) :
    (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).paired
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i)=
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf (ρ i) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  change _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf
    (ρ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).symm (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i)))=_
  rw [Equiv.symm_apply_apply]

theorem cofiniteTangentialPairing_finite_vertex {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) :
    cofiniteTangentPairingElement θ d hθ hd hb i (ρ i)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i)=
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf
          (cofiniteTangentialCanonicalIndex ρ i) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  have hv:=cofiniteTangentPairingElement_vertex_eq θ d hθ hd hb i (ρ i) (hθρ i)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (finRotate n (ρ i))))
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate Q hf i).symm
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate Q hf (finRotate n (ρ i))).symm
  change cofiniteTangentPairingElement θ d hθ hd hb i (ρ i)
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (finRotate n (ρ i))
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hv

/-- One original canonical step crosses the literal outgoing side and then
chooses the actual next outgoing side, with the exact generated-group index. -/
theorem cofiniteTangentialCanonicalStep {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n)
    (g:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S (g,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
      (g*(S.generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i))⁻¹,
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf (cofiniteTangentialCanonicalIndex ρ i)) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let E:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf
  let hV:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPairing_preserves_vertices Q hf S
  let a:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i
  let c:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap Q hf S hV a
  let j:=cofiniteTangentialCanonicalIndex ρ i
  have hmap:S.element (E i) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf j:=by
    rw [cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ i,
      cofiniteTangentialPairing_finite_vertex θ d hθ hd hb hf ρ hθρ i]
  have hci:c.val.1=j:=by
    apply _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap_vertex Q hf S hV a).trans hmap
  have hcs:c.val.2=E (ρ i):=
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap_side Q hf S hV a).trans
      (cofiniteTangentialSidePairing_paired_index θ d hθ hd hb hf ρ hρ hθρ i)
  have hne:E (ρ i)≠E j:=E.injective.ne (Q.next_ne_self (ρ i)).symm
  change (g*(S.generator a.val.2)⁻¹,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertexOtherFlag Q hf c)=_
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Prod.ext
    · exact hci
    · change _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertexOtherSide Q hf c.val.1 c.val.2=E j
      rw [hci,hcs]
      exact ite_eq_right hne

/-- The literal canonical word uses the actual original side generators. -/
def cofiniteTangentialCanonicalWord {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) :
    ℕ→(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated
  | 0=>1
  | j+1=>cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j*
      ((cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).generator
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf
          (((cofiniteTangentialCanonicalIndex ρ)^[j]) i)))⁻¹

/-- Every true canonical iterate retains its exact independent side label
and the recursively prescribed literal generated word. -/
theorem cofiniteTangentialCanonicalWord_flag_state {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (j:ℕ) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
      (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j,
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf (((cofiniteTangentialCanonicalIndex ρ)^[j]) i)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply',ih,cofiniteTangentialCanonicalStep,
      Function.iterate_succ_apply']
    rfl

/-- The same word, evaluated in the actual native isometry group. -/
def cofiniteTangentialCanonicalNativeWord {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (i:Fin n) : ℕ→(ℍ≃ᵢℍ)
  | 0=>1
  | j+1=>cofiniteTangentialCanonicalNativeWord θ d hθ hd hb ρ i j*
      (cofiniteTangentPairingElement θ d hθ hd hb
        (((cofiniteTangentialCanonicalIndex ρ)^[j]) i)
        (ρ (((cofiniteTangentialCanonicalIndex ρ)^[j]) i)))⁻¹

theorem cofiniteTangentialCanonicalWord_value {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (j:ℕ) :
    (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val=
      cofiniteTangentialCanonicalNativeWord θ d hθ hd hb ρ i j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val*
      ((cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).element
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf
          (((cofiniteTangentialCanonicalIndex ρ)^[j]) i)))⁻¹=_
    rw [ih,cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ]
    rfl

/-- The original Poincare copy of every canonical state is the literal word
and its actual iterated original vertex, ready for the actual local fan. -/
theorem cofiniteTangentialCanonicalWord_copy {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (j:ℕ) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i))=
      (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j,
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf (((cofiniteTangentialCanonicalIndex ρ)^[j]) i)) := by
  dsimp only
  rw [cofiniteTangentialCanonicalWord_flag_state]
  rfl


/-- The canonical generated-group word evaluates to the same literal native
word used by the actual variable-angle frame walk. -/
theorem cofiniteTangentialCanonicalWord_nativeAngularWalkWord {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (j:ℕ) :
    (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val=
      nativeAngularWalkWord
        (fun k=>cofiniteTangentPairingElement θ d hθ hd hb
          (((cofiniteTangentialCanonicalIndex ρ)^[k]) i)
          (ρ (((cofiniteTangentialCanonicalIndex ρ)^[k]) i))) j := by
  rw [cofiniteTangentialCanonicalWord_value]
  induction j with
  | zero => rfl
  | succ j ih =>
    change cofiniteTangentialCanonicalNativeWord θ d hθ hd hb ρ i j*
      (cofiniteTangentPairingElement θ d hθ hd hb
        (((cofiniteTangentialCanonicalIndex ρ)^[j]) i)
        (ρ (((cofiniteTangentialCanonicalIndex ρ)^[j]) i)))⁻¹=_
    rw [ih]
    rfl

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- Actual evaluated canonical words send the actual current vertex to the
original one, for all iterates before imposing any angular closure relation. -/
theorem cofiniteTangentialCanonicalWord_center {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (j:ℕ) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (((cofiniteTangentialCanonicalIndex ρ)^[j]) i))=
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let τ:=cofiniteTangentialCanonicalIndex ρ
  induction j with
  | zero => rfl
  | succ j ih =>
    change ((cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val*
      ((cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).element
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf (τ^[j] i)))⁻¹)
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (τ^[j+1] i))=_
    rw [cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ,
      Function.iterate_succ_apply']
    change (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val
      ((cofiniteTangentPairingElement θ d hθ hd hb (τ^[j] i) (ρ (τ^[j] i)))⁻¹
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (τ (τ^[j] i))))=_
    rw [←cofiniteTangentialPairing_finite_vertex θ d hθ hd hb hf ρ hθρ (τ^[j] i),
      IsometryEquiv.inv_apply_self]
    exact ih

/-- Every prescribed complete angular period produces the actual original
canonical vertex cycle, with literal side labels and indexed copy pieces. -/
theorem cofiniteTangential_canonical_cycle_conditions {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) :
    _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonCanonicalCycleConditions (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf
      (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let τ:=cofiniteTangentialCanonicalIndex ρ
  intro i
  obtain ⟨N,hN,hClose,hAngle⟩:=hPeriod i
  let A:ℕ→(ℍ≃ᵢℍ):=fun j=>cofiniteTangentPairingElement θ d hθ hd hb (τ^[j] i) (ρ (τ^[j] i))
  let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)
  have hw:Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate Q hf i).symm
  obtain ⟨r,hr,hFan⟩:=cofiniteTangential_finite_cycle_ball_fan θ d hθ hd hb ρ hρ hθρ hf i w hw N hN hAngle
  obtain ⟨hCover,hDis⟩:=hFan r hr le_rfl
  have hwP:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc _
  rw [hwP] at hCover hDis
  have hWord:cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i N=1:=by
    apply Subtype.ext
    rw [cofiniteTangentialCanonicalWord_nativeAngularWalkWord]
    exact cofiniteTangential_finite_word_period θ d hθ hd hb ρ hρ hθρ hf i N (by omega) hClose hAngle
  have hState:((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[N]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
      (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i):=by
    rw [cofiniteTangentialCanonicalWord_flag_state,hWord]
    change ((1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf (((ρ.trans (finRotate n))^[N]) i)):
      _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S)=(1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)
    rw [hClose]
  have hPiece (j:ℕ) (U:Set ℍ):
      (fun x:ℍ=>(cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val x) ''
        (U∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (τ^[j] i)) r)=
      (nativeAngularWalkWord A j '' U)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i) r:=by
    let W:ℍ≃ᵢℍ:=(cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val
    change W '' (U∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (τ^[j] i)) r)=_
    rw [Set.image_inter W.injective,W.image_ball,
      cofiniteTangentialCanonicalWord_center θ d hθ hd hb hf ρ hρ hθρ i j]
    rw [show W=nativeAngularWalkWord A j by
      exact cofiniteTangentialCanonicalWord_nativeAngularWalkWord θ d hθ hd hb hf ρ hρ hθρ i j]
  have hC (j:Fin N):S.vertexCyclePiece
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j.val])
        (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i))) r=
      (nativeAngularWalkWord A j.val '' P.carrier)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i) r:=by
    rw [cofiniteTangentialCanonicalWord_copy]
    exact hPiece j.val P.carrier
  have hI (j:Fin N):S.vertexCycleInteriorPiece
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j.val])
        (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i))) r=
      (nativeAngularWalkWord A j.val '' P.interior)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i) r:=by
    rw [cofiniteTangentialCanonicalWord_copy]
    exact hPiece j.val P.interior
  refine ⟨N-1,r,hr,?_,?_,?_⟩
  · simpa only [show N-1+1=N by omega] using hState
  · rw [show N-1+1=N by omega]
    exact (iUnion_congr hC).trans hCover
  · rw [show N-1+1=N by omega]
    intro j k hjk
    rw [hI j,hI k]
    exact hDis hjk

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
/-- The literal outer blocks, retaining each order-two base mark. -/
def cofiniteConstructionMarkAngles (α : ℝ) : List ℕ → List ℝ
  | [] => []
  | m :: ms => if m = 2 then α :: cofiniteConstructionMarkAngles α ms
    else α :: cofiniteConstructionConeAngle m :: cofiniteConstructionMarkAngles α ms

def cofiniteConstructionSideAngles (α : ℝ) (g : ℕ) (ms : List ℕ) : List ℝ :=
  List.replicate (4*g) α ++ cofiniteConstructionMarkAngles α ms

theorem cofiniteConstructionAngles_eq_sideAngles (g : ℕ) (ms : List ℕ) (last : ℕ) :
    cofiniteConstructionAngles g ms last =
      cofiniteConstructionSideAngles (cofiniteConstructionBaseAngle g ms last) g ms := by
  have h (α : ℝ) (ls : List ℕ) :
      ls.flatMap (fun m => [α] ++ if m = 2 then [] else [cofiniteConstructionConeAngle m]) =
        cofiniteConstructionMarkAngles α ls := by
    induction ls with
    | nil => rfl
    | cons m ls ih =>
      by_cases hm : m = 2 <;>
        simpa only [List.flatMap_cons, cofiniteConstructionMarkAngles, hm, ite_true, ite_false,
          List.append_nil, List.cons_append, List.nil_append] using congrArg (fun x =>
            if m=2 then α::x else α::cofiniteConstructionConeAngle m::x) ih
  exact congrArg (fun x => List.replicate (4*g) _ ++ x) (h _ _)

/-- Actual single outer edges are fixed and actual two-edge blocks exchange their sides. -/
def cofiniteConstructionMarkPairNat : List ℕ → ℕ → ℕ
  | [], i => i
  | m :: ms, i => if m = 2 then
      if i = 0 then 0 else 1 + cofiniteConstructionMarkPairNat ms (i-1)
    else if i < 2 then 1-i else 2 + cofiniteConstructionMarkPairNat ms (i-2)

/-- Each handle exchanges sides zero/two and one/three in its unchanged four-edge block. -/
def cofiniteConstructionPairNat : ℕ → List ℕ → ℕ → ℕ
  | 0, ms, i => cofiniteConstructionMarkPairNat ms i
  | g+1, ms, i => if i < 4 then if i < 2 then i+2 else i-2
    else 4 + cofiniteConstructionPairNat g ms (i-4)

theorem cofiniteConstructionMarkPairNat_involutive (ms : List ℕ) :
    Function.Involutive (cofiniteConstructionMarkPairNat ms) := by
  induction ms with
  | nil => intro i; rfl
  | cons m ms ih =>
    dsimp only [Function.Involutive] at ih
    intro i
    by_cases hm : m = 2
    · cases i with
      | zero => simp [cofiniteConstructionMarkPairNat, hm]
      | succ i =>
        have hstep (j : ℕ) : cofiniteConstructionMarkPairNat (m::ms) (j+1) =
            1+cofiniteConstructionMarkPairNat ms j := by
          simp [cofiniteConstructionMarkPairNat, hm]
        rw [hstep, show 1+cofiniteConstructionMarkPairNat ms i=cofiniteConstructionMarkPairNat ms i+1 by omega,
          hstep, ih]
        omega
    · cases i with
      | zero => simp [cofiniteConstructionMarkPairNat, hm]
      | succ i =>
        cases i with
        | zero => simp [cofiniteConstructionMarkPairNat, hm]
        | succ i =>
          change cofiniteConstructionMarkPairNat (m::ms)
            (cofiniteConstructionMarkPairNat (m::ms) (i+2)) = i+2
          have hstep (j : ℕ) : cofiniteConstructionMarkPairNat (m::ms) (j+2) =
              2+cofiniteConstructionMarkPairNat ms j := by
            rw [cofiniteConstructionMarkPairNat, ite_eq_right hm, ite_eq_right (by omega), Nat.add_sub_cancel_right]
          rw [hstep, show 2+cofiniteConstructionMarkPairNat ms i=cofiniteConstructionMarkPairNat ms i+2 by omega,
            hstep, ih]
          omega

theorem cofiniteConstructionPairNat_involutive (g : ℕ) (ms : List ℕ) :
    Function.Involutive (cofiniteConstructionPairNat g ms) := by
  induction g with
  | zero => exact cofiniteConstructionMarkPairNat_involutive ms
  | succ g ih =>
    dsimp only [Function.Involutive] at ih
    intro i
    by_cases hi : i < 4
    · interval_cases i <;> simp [cofiniteConstructionPairNat]
    · obtain ⟨j, rfl⟩ : ∃j, i = 4+j := ⟨i-4, by omega⟩
      have hstep (l : ℕ) : cofiniteConstructionPairNat (g+1) ms (4+l) =
          4+cofiniteConstructionPairNat g ms l := by
        rw [cofiniteConstructionPairNat, ite_eq_right (by omega), show 4+l-4=l by omega]
      rw [hstep, hstep, ih]

theorem cofiniteConstructionMarkPairNat_bound (α : ℝ) (ms : List ℕ)
    (i : ℕ) (hi : i < (cofiniteConstructionMarkAngles α ms).length) :
    cofiniteConstructionMarkPairNat ms i < (cofiniteConstructionMarkAngles α ms).length := by
  induction ms generalizing i with
  | nil => simp [cofiniteConstructionMarkAngles] at hi
  | cons m ms ih =>
    by_cases hm : m = 2
    · cases i with
      | zero => simp [cofiniteConstructionMarkPairNat, cofiniteConstructionMarkAngles, hm]
      | succ i =>
        have hi' : i < (cofiniteConstructionMarkAngles α ms).length := by
          simpa [cofiniteConstructionMarkAngles, hm] using hi
        have hh := ih i hi'
        simpa [cofiniteConstructionMarkPairNat, cofiniteConstructionMarkAngles, hm, Nat.add_comm] using hh
    · cases i with
      | zero => simp [cofiniteConstructionMarkPairNat, cofiniteConstructionMarkAngles, hm]
      | succ i =>
        cases i with
        | zero => simp [cofiniteConstructionMarkPairNat, cofiniteConstructionMarkAngles, hm]
        | succ i =>
          have hi' : i < (cofiniteConstructionMarkAngles α ms).length := by
            simpa [cofiniteConstructionMarkAngles, hm] using hi
          have hh := ih i hi'
          change cofiniteConstructionMarkPairNat (m::ms) (i+2) < _
          rw [cofiniteConstructionMarkPairNat, ite_eq_right hm, ite_eq_right (by omega), Nat.add_sub_cancel_right]
          simp only [cofiniteConstructionMarkAngles, hm, ite_false, List.length_cons]
          omega

theorem cofiniteConstructionSideAngles_handle (α : ℝ) (g : ℕ) (ms : List ℕ) :
    cofiniteConstructionSideAngles α (g+1) ms =
      α :: α :: α :: α :: cofiniteConstructionSideAngles α g ms := by
  dsimp only [cofiniteConstructionSideAngles]
  rw [show 4*(g+1) = 4+4*g by omega, List.replicate_add]
  rfl

theorem cofiniteConstructionPairNat_bound (α : ℝ) (g : ℕ) (ms : List ℕ)
    (i : ℕ) (hi : i < (cofiniteConstructionSideAngles α g ms).length) :
    cofiniteConstructionPairNat g ms i < (cofiniteConstructionSideAngles α g ms).length := by
  induction g generalizing i with
  | zero => exact cofiniteConstructionMarkPairNat_bound α ms i hi
  | succ g ih =>
    rw [cofiniteConstructionSideAngles_handle] at hi ⊢
    simp only [List.length_cons] at hi ⊢
    by_cases hi4 : i < 4
    · interval_cases i <;> simp [cofiniteConstructionPairNat]
    · obtain ⟨j, rfl⟩ : ∃j, i = 4+j := ⟨i-4, by omega⟩
      have hj : j < (cofiniteConstructionSideAngles α g ms).length := by omega
      have hh := ih j hj
      rw [cofiniteConstructionPairNat, ite_eq_right (by omega)]
      rw [show 4+j-4=j by omega]
      omega

def cofiniteConstructionPairing (g : ℕ) (ms : List ℕ) (last : ℕ) :
    Equiv.Perm (Fin (cofiniteConstructionAngles g ms last).length) :=
  let f : Fin (cofiniteConstructionAngles g ms last).length →
      Fin (cofiniteConstructionAngles g ms last).length := fun i =>
    ⟨cofiniteConstructionPairNat g ms i.val, by
      have hi := i.isLt
      have hlen := congrArg List.length (cofiniteConstructionAngles_eq_sideAngles g ms last)
      have hib : i.val < (cofiniteConstructionSideAngles (cofiniteConstructionBaseAngle g ms last) g ms).length :=
        hi.trans_eq hlen
      exact (cofiniteConstructionPairNat_bound _ _ _ _ hib).trans_eq hlen.symm⟩
  (show Function.Involutive f from fun i => Fin.ext (cofiniteConstructionPairNat_involutive g ms i.val)).toPerm

theorem cofiniteConstructionPairing_val (g : ℕ) (ms : List ℕ) (last : ℕ)
    (i : Fin (cofiniteConstructionAngles g ms last).length) :
    (cofiniteConstructionPairing g ms last i).val = cofiniteConstructionPairNat g ms i.val := rfl

theorem cofiniteConstructionPairing_involutive (g : ℕ) (ms : List ℕ) (last : ℕ) :
    Function.Involutive (cofiniteConstructionPairing g ms last) := by
  intro i
  apply Fin.ext
  exact cofiniteConstructionPairNat_involutive g ms i.val

theorem cofiniteConstructionMarkAngles_head (α : ℝ) (ms : List ℕ) :
    (cofiniteConstructionMarkAngles α ms).getD 0 α = α := by
  cases ms with
  | nil => rfl
  | cons m ms => by_cases hm : m = 2 <;> simp [cofiniteConstructionMarkAngles, hm]

theorem cofiniteConstructionSideAngles_head (α : ℝ) (g : ℕ) (ms : List ℕ) :
    (cofiniteConstructionSideAngles α g ms).getD 0 α = α := by
  cases g with
  | zero => exact cofiniteConstructionMarkAngles_head α ms
  | succ g => rw [cofiniteConstructionSideAngles_handle]; rfl

private theorem cofiniteConstruction_getD_cons (a : ℝ) (ls : List ℝ) (i : ℕ) (d : ℝ) :
    (a::ls).getD (i+1) d = ls.getD i d := rfl

private theorem cofiniteConstruction_getD_four (a : ℝ) (ls : List ℝ) (i : ℕ) (d : ℝ) :
    (a::a::a::a::ls).getD (i+4) d = ls.getD i d := rfl

/-- The actual original angle after the paired side equals the starting angle.
The default base angle handles the unique final-to-first wrap. -/
theorem cofiniteConstructionMarkPairNat_getD (α : ℝ) (ms : List ℕ) (i : ℕ) :
    (cofiniteConstructionMarkAngles α ms).getD (cofiniteConstructionMarkPairNat ms i+1) α =
      (cofiniteConstructionMarkAngles α ms).getD i α := by
  induction ms generalizing i with
  | nil => simp [cofiniteConstructionMarkAngles]
  | cons m ms ih =>
    by_cases hm : m = 2
    · cases i with
      | zero =>
        rw [cofiniteConstructionMarkPairNat, ite_eq_left hm, ite_eq_left rfl,
          cofiniteConstructionMarkAngles, ite_eq_left hm]
        exact cofiniteConstructionMarkAngles_head α ms
      | succ i =>
        rw [cofiniteConstructionMarkPairNat, ite_eq_left hm, ite_eq_right (by omega)]
        rw [show i+1-1=i by omega, cofiniteConstructionMarkAngles, ite_eq_left hm]
        rw [show 1+cofiniteConstructionMarkPairNat ms i+1=(cofiniteConstructionMarkPairNat ms i+1)+1 by omega,
          cofiniteConstruction_getD_cons, cofiniteConstruction_getD_cons]
        exact ih i
    · cases i with
      | zero =>
        rw [cofiniteConstructionMarkPairNat, ite_eq_right hm, ite_eq_left (by omega)]
        rw [cofiniteConstructionMarkAngles, ite_eq_right hm]
        exact cofiniteConstructionMarkAngles_head α ms
      | succ i =>
        cases i with
        | zero => simp [cofiniteConstructionMarkAngles, cofiniteConstructionMarkPairNat, hm]
        | succ i =>
          change (cofiniteConstructionMarkAngles α (m::ms)).getD
            (cofiniteConstructionMarkPairNat (m::ms) (i+2)+1) α = _
          rw [cofiniteConstructionMarkPairNat, ite_eq_right hm, ite_eq_right (by omega), Nat.add_sub_cancel_right]
          rw [cofiniteConstructionMarkAngles, ite_eq_right hm]
          rw [show 2+cofiniteConstructionMarkPairNat ms i+1=
            ((cofiniteConstructionMarkPairNat ms i+1)+1)+1 by omega,
            cofiniteConstruction_getD_cons, cofiniteConstruction_getD_cons]
          rw [cofiniteConstruction_getD_cons, cofiniteConstruction_getD_cons]
          exact ih i

theorem cofiniteConstructionPairNat_getD (α : ℝ) (g : ℕ) (ms : List ℕ) (i : ℕ) :
    (cofiniteConstructionSideAngles α g ms).getD (cofiniteConstructionPairNat g ms i+1) α =
      (cofiniteConstructionSideAngles α g ms).getD i α := by
  induction g generalizing i with
  | zero => exact cofiniteConstructionMarkPairNat_getD α ms i
  | succ g ih =>
    by_cases hi : i < 4
    · interval_cases i
      · simp [cofiniteConstructionSideAngles_handle, cofiniteConstructionPairNat]
      · rw [cofiniteConstructionPairNat, ite_eq_left (by omega), ite_eq_left (by omega)]
        rw [cofiniteConstructionSideAngles_handle]
        exact cofiniteConstructionSideAngles_head α g ms
      · simp [cofiniteConstructionSideAngles_handle, cofiniteConstructionPairNat]
      · simp [cofiniteConstructionSideAngles_handle, cofiniteConstructionPairNat]
    · obtain ⟨j, rfl⟩ : ∃j, i = 4+j := ⟨i-4, by omega⟩
      rw [cofiniteConstructionPairNat, ite_eq_right (by omega), show 4+j-4=j by omega,
        cofiniteConstructionSideAngles_handle]
      change ([α,α,α,α]++cofiniteConstructionSideAngles α g ms).getD
        (4+cofiniteConstructionPairNat g ms j+1) α =
        ([α,α,α,α]++cofiniteConstructionSideAngles α g ms).getD (4+j) α
      rw [show 4+cofiniteConstructionPairNat g ms j+1=(cofiniteConstructionPairNat g ms j+1)+4 by omega,
        show 4+j=j+4 by omega]
      simp only [List.cons_append, List.nil_append]
      rw [cofiniteConstruction_getD_four, cofiniteConstruction_getD_four]
      exact ih j

private theorem cofiniteConstruction_finRotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val = if i.val+1=n then 0 else i.val+1 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases hi : i = Fin.last n
    · subst i
      simp
    · have hn : i.val+1 ≠ n+1 := by
        intro he
        apply hi
        apply Fin.ext
        change i.val=n
        omega
      simp only [hi, ite_false, hn]

theorem cofiniteConstructionPairing_angle_profile (g : ℕ) (ms : List ℕ) (last : ℕ)
    (i : Fin (cofiniteConstructionAngles g ms last).length) :
    (cofiniteConstructionAngles g ms last)[i] =
      (cofiniteConstructionAngles g ms last)[finRotate _ (cofiniteConstructionPairing g ms last i)] := by
  let L := cofiniteConstructionAngles g ms last
  let α := cofiniteConstructionBaseAngle g ms last
  let j := cofiniteConstructionPairing g ms last i
  have hprofile : L.getD (j.val+1) α = L.getD i.val α := by
    rw [cofiniteConstructionPairing_val]
    dsimp only [L]
    simpa only [cofiniteConstructionAngles_eq_sideAngles] using
      cofiniteConstructionPairNat_getD α g ms i.val
  have hhead : L.getD 0 α = α := by
    dsimp only [L]
    rw [cofiniteConstructionAngles_eq_sideAngles]
    exact cofiniteConstructionSideAngles_head α g ms
  have hrot := cofiniteConstruction_finRotate_val j
  have hget : L.getD i.val α = L.getD (finRotate L.length j).val α := by
    by_cases he : j.val+1=L.length
    · rw [ite_eq_left he] at hrot
      rw [hrot, hhead]
      rw [he, List.getD_eq_default L α (le_refl _)] at hprofile
      exact hprofile.symm
    · rw [ite_eq_right he] at hrot
      rw [hrot]
      exact hprofile.symm
  simpa only [List.getD_eq_getElem L α i.isLt,
    List.getD_eq_getElem L α (finRotate L.length j).isLt, Fin.getElem_fin, L, j] using hget


end LowDimensionalTopology.Geometry.Fuchsian


namespace LowDimensionalTopology.Geometry.Fuchsian
open Set
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- This reverses the three nonzero handle positions and preserves their labels. -/
def cofiniteConstructionHandleBaseNat (i : ℕ) : ℕ :=
  if i=1 then 3 else if i=3 then 1 else i

theorem cofiniteConstructionHandleBaseNat_involutive :
    Function.Involutive cofiniteConstructionHandleBaseNat := by
  intro i
  by_cases h1 : i=1
  · subst i; rfl
  by_cases h3 : i=3
  · subst i; rfl
  simp only [cofiniteConstructionHandleBaseNat, h1, h3, ite_false]

theorem cofiniteConstructionHandleBaseNat_lt_four (i : ℕ) (hi : i<4) :
    cofiniteConstructionHandleBaseNat i < 4 := by
  interval_cases i <;> decide

/-- Each outer block contributes its initial marked base corner, with its own list label. -/
def cofiniteConstructionMarkBaseNat : List ℕ → ℕ → ℕ
  | [], i => i
  | _::_, 0 => 0
  | m::ms, i+1 => (if m=2 then 1 else 2)+cofiniteConstructionMarkBaseNat ms i

/-- Base-cycle order on each handle is zero, three, two, one. -/
def cofiniteConstructionBaseNat : ℕ → List ℕ → ℕ → ℕ
  | 0, ms, i => cofiniteConstructionMarkBaseNat ms i
  | g+1, ms, i => if i<4 then cofiniteConstructionHandleBaseNat i
    else 4+cofiniteConstructionBaseNat g ms (i-4)

theorem cofiniteConstructionMarkBaseNat_zero (ms : List ℕ) :
    cofiniteConstructionMarkBaseNat ms 0=0 := by cases ms <;> rfl

theorem cofiniteConstructionBaseNat_zero (g : ℕ) (ms : List ℕ) :
    cofiniteConstructionBaseNat g ms 0=0 := by
  cases g with
  | zero => exact cofiniteConstructionMarkBaseNat_zero ms
  | succ g => rfl

theorem cofiniteConstructionMarkBaseNat_injective (ms : List ℕ) :
    Function.Injective (cofiniteConstructionMarkBaseNat ms) := by
  induction ms with
  | nil => exact fun _ _ h => h
  | cons m ms ih =>
    intro i j hij
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [cofiniteConstructionMarkBaseNat] at hij
        split_ifs at hij <;> omega
    | succ i =>
      cases j with
      | zero =>
        simp only [cofiniteConstructionMarkBaseNat] at hij
        split_ifs at hij <;> omega
      | succ j =>
        simp only [cofiniteConstructionMarkBaseNat] at hij
        exact congrArg Nat.succ (ih (Nat.add_left_cancel hij))

theorem cofiniteConstructionBaseNat_injective (g : ℕ) (ms : List ℕ) :
    Function.Injective (cofiniteConstructionBaseNat g ms) := by
  induction g with
  | zero => exact cofiniteConstructionMarkBaseNat_injective ms
  | succ g ih =>
    intro i j hij
    by_cases hi : i<4 <;> by_cases hj : j<4
    · simp only [cofiniteConstructionBaseNat, hi, hj, ite_true] at hij
      exact cofiniteConstructionHandleBaseNat_involutive.injective hij
    · have hb := cofiniteConstructionHandleBaseNat_lt_four i hi
      simp only [cofiniteConstructionBaseNat, hi, hj, ite_true, ite_false] at hij
      omega
    · have hb := cofiniteConstructionHandleBaseNat_lt_four j hj
      simp only [cofiniteConstructionBaseNat, hi, hj, ite_true, ite_false] at hij
      omega
    · simp only [cofiniteConstructionBaseNat, hi, hj, ite_false] at hij
      have he := ih (Nat.add_left_cancel hij)
      omega

theorem cofiniteConstructionMarkBaseNat_bound (α : ℝ) (ms : List ℕ) (i : ℕ)
    (hi : i<ms.length) :
    cofiniteConstructionMarkBaseNat ms i < (cofiniteConstructionMarkAngles α ms).length := by
  induction ms generalizing i with
  | nil => simp at hi
  | cons m ms ih =>
    cases i with
    | zero => by_cases hm : m=2 <;> simp [cofiniteConstructionMarkBaseNat, cofiniteConstructionMarkAngles, hm]
    | succ i =>
      have hi' : i<ms.length := by simpa using hi
      have hh := ih i hi'
      by_cases hm : m=2 <;>
        simp only [cofiniteConstructionMarkBaseNat, cofiniteConstructionMarkAngles, hm,
          ite_true, ite_false, List.length_cons] <;> omega

theorem cofiniteConstructionBaseNat_bound (α : ℝ) (g : ℕ) (ms : List ℕ) (i : ℕ)
    (hi : i<4*g+ms.length) :
    cofiniteConstructionBaseNat g ms i < (cofiniteConstructionSideAngles α g ms).length := by
  induction g generalizing i with
  | zero => exact cofiniteConstructionMarkBaseNat_bound α ms i (by simpa using hi)
  | succ g ih =>
    rw [cofiniteConstructionSideAngles_handle]
    simp only [List.length_cons]
    by_cases hi4 : i<4
    · rw [cofiniteConstructionBaseNat, ite_eq_left hi4]
      have hh := cofiniteConstructionHandleBaseNat_lt_four i hi4
      omega
    · rw [cofiniteConstructionBaseNat, ite_eq_right hi4]
      have hh := ih (i-4) (by omega)
      omega

theorem cofiniteConstructionMarkBaseNat_full (α : ℝ) (ms : List ℕ) :
    cofiniteConstructionMarkBaseNat ms ms.length = (cofiniteConstructionMarkAngles α ms).length := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    by_cases hm : m=2 <;>
      simp only [List.length_cons, cofiniteConstructionMarkBaseNat, cofiniteConstructionMarkAngles,
        hm, ite_true, ite_false, ih] <;> omega

theorem cofiniteConstructionBaseNat_full (α : ℝ) (g : ℕ) (ms : List ℕ) :
    cofiniteConstructionBaseNat g ms (4*g+ms.length) = (cofiniteConstructionSideAngles α g ms).length := by
  induction g with
  | zero => simpa only [cofiniteConstructionBaseNat, cofiniteConstructionSideAngles,
      Nat.mul_zero, Nat.zero_add, List.replicate_zero, List.nil_append] using
      cofiniteConstructionMarkBaseNat_full α ms
  | succ g ih =>
    rw [cofiniteConstructionBaseNat, ite_eq_right (by omega), cofiniteConstructionSideAngles_handle]
    simp only [List.length_cons]
    rw [show 4*(g+1)+ms.length-4=4*g+ms.length by omega, ih]
    omega

theorem cofiniteConstructionMarkPairNat_shift (m : ℕ) (ms : List ℕ) (i : ℕ) :
    cofiniteConstructionMarkPairNat (m::ms) ((if m=2 then 1 else 2)+i) =
      (if m=2 then 1 else 2)+cofiniteConstructionMarkPairNat ms i := by
  by_cases hm : m=2
  · simp [cofiniteConstructionMarkPairNat, hm]
  · rw [ite_eq_right hm, cofiniteConstructionMarkPairNat, ite_eq_right hm,
      ite_eq_right (by omega), show 2+i-2=i by omega]

theorem cofiniteConstructionPairNat_shift (g : ℕ) (ms : List ℕ) (i : ℕ) :
    cofiniteConstructionPairNat (g+1) ms (4+i) = 4+cofiniteConstructionPairNat g ms i := by
  rw [cofiniteConstructionPairNat, ite_eq_right (by omega), show 4+i-4=i by omega]

theorem cofiniteConstructionMarkBaseNat_step (ms : List ℕ) (i : ℕ) :
    cofiniteConstructionMarkPairNat ms (cofiniteConstructionMarkBaseNat ms i)+1 =
      cofiniteConstructionMarkBaseNat ms (i+1) := by
  induction ms generalizing i with
  | nil => rfl
  | cons m ms ih =>
    cases i with
    | zero =>
      by_cases hm : m=2 <;>
        simp [cofiniteConstructionMarkBaseNat, cofiniteConstructionMarkPairNat, hm,
          cofiniteConstructionMarkBaseNat_zero]
    | succ i =>
      rw [cofiniteConstructionMarkBaseNat, cofiniteConstructionMarkPairNat_shift]
      change (if m=2 then 1 else 2)+cofiniteConstructionMarkPairNat ms
        (cofiniteConstructionMarkBaseNat ms i)+1 =
        (if m=2 then 1 else 2)+cofiniteConstructionMarkBaseNat ms (i+1)
      have hh := ih i
      omega

theorem cofiniteConstructionBaseNat_step (g : ℕ) (ms : List ℕ) (i : ℕ) :
    cofiniteConstructionPairNat g ms (cofiniteConstructionBaseNat g ms i)+1 =
      cofiniteConstructionBaseNat g ms (i+1) := by
  induction g generalizing i with
  | zero => exact cofiniteConstructionMarkBaseNat_step ms i
  | succ g ih =>
    by_cases hi : i<4
    · interval_cases i <;>
        simp [cofiniteConstructionBaseNat, cofiniteConstructionHandleBaseNat,
          cofiniteConstructionPairNat, cofiniteConstructionBaseNat_zero]
    · obtain ⟨j,rfl⟩ : ∃j,i=4+j := ⟨i-4,by omega⟩
      rw [cofiniteConstructionBaseNat, ite_eq_right (by omega), show 4+j-4=j by omega,
        cofiniteConstructionPairNat_shift]
      rw [cofiniteConstructionBaseNat, ite_eq_right (by omega),
        show 4+j+1-4=j+1 by omega]
      have hh := ih j
      omega

def cofiniteConstructionBaseIndex (g : ℕ) (ms : List ℕ) (last : ℕ)
    (i : Fin (4*g+ms.length)) : Fin (cofiniteConstructionAngles g ms last).length :=
  ⟨cofiniteConstructionBaseNat g ms i.val, by
    have hlen := congrArg List.length (cofiniteConstructionAngles_eq_sideAngles g ms last)
    exact (cofiniteConstructionBaseNat_bound _ g ms i.val i.isLt).trans_eq hlen.symm⟩

theorem cofiniteConstructionBaseIndex_val (g : ℕ) (ms : List ℕ) (last : ℕ)
    (i : Fin (4*g+ms.length)) :
    (cofiniteConstructionBaseIndex g ms last i).val = cofiniteConstructionBaseNat g ms i.val := rfl

theorem cofiniteConstructionBaseIndex_injective (g : ℕ) (ms : List ℕ) (last : ℕ) :
    Function.Injective (cofiniteConstructionBaseIndex g ms last) := by
  intro i j hij
  exact Fin.ext (cofiniteConstructionBaseNat_injective g ms (congrArg Fin.val hij))

theorem cofiniteConstructionBaseIndex_next (g : ℕ) (ms : List ℕ) (last : ℕ)
    (i : Fin (4*g+ms.length)) :
    cofiniteConstructionBaseIndex g ms last (finRotate _ i) =
      finRotate _ (cofiniteConstructionPairing g ms last (cofiniteConstructionBaseIndex g ms last i)) := by
  let B := 4*g+ms.length
  let N := (cofiniteConstructionAngles g ms last).length
  have hstep := cofiniteConstructionBaseNat_step g ms i.val
  have hfull : cofiniteConstructionBaseNat g ms B=N := by
    have hlen := congrArg List.length (cofiniteConstructionAngles_eq_sideAngles g ms last)
    exact (cofiniteConstructionBaseNat_full _ g ms).trans hlen.symm
  have hrotB := cofiniteConstruction_finRotate_val i
  have hrotN := cofiniteConstruction_finRotate_val
    (cofiniteConstructionPairing g ms last (cofiniteConstructionBaseIndex g ms last i))
  rw [cofiniteConstructionPairing_val, cofiniteConstructionBaseIndex_val] at hrotN
  apply Fin.ext
  rw [cofiniteConstructionBaseIndex_val, hrotB, hrotN]
  change cofiniteConstructionBaseNat g ms (if i.val+1=B then 0 else i.val+1) =
    if cofiniteConstructionPairNat g ms (cofiniteConstructionBaseNat g ms i.val)+1=N then 0
      else cofiniteConstructionPairNat g ms (cofiniteConstructionBaseNat g ms i.val)+1
  by_cases hi : i.val+1=B
  · rw [ite_eq_left hi, cofiniteConstructionBaseNat_zero, hstep, hi, hfull, ite_eq_left rfl]
  · have hb : i.val+1<B := by have := i.isLt; omega
    have hbn : cofiniteConstructionBaseNat g ms (i.val+1)<N := by
      have hlen := congrArg List.length (cofiniteConstructionAngles_eq_sideAngles g ms last)
      exact (cofiniteConstructionBaseNat_bound _ g ms _ hb).trans_eq hlen.symm
    have hn : cofiniteConstructionPairNat g ms (cofiniteConstructionBaseNat g ms i.val)+1≠N := by
      rw [hstep]
      omega
    rw [ite_eq_right hi, ite_eq_right hn]
    exact hstep.symm

def cofiniteConstructionVertexStep (g : ℕ) (ms : List ℕ) (last : ℕ) :
    Equiv.Perm (Fin (cofiniteConstructionAngles g ms last).length) :=
  (cofiniteConstructionPairing g ms last).trans (finRotate _)

theorem cofiniteConstructionBaseIndex_iterate (g : ℕ) (ms : List ℕ) (last : ℕ)
    (j : ℕ) (i : Fin (4*g+ms.length)) :
    ((cofiniteConstructionVertexStep g ms last)^[j]) (cofiniteConstructionBaseIndex g ms last i) =
      cofiniteConstructionBaseIndex g ms last ((finRotate _)^[j] i) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    exact (cofiniteConstructionBaseIndex_next g ms last _).symm

/-- All independently labelled base marks belong to one actual natural vertex cycle. -/
theorem cofiniteConstructionBaseIndex_one_cycle (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 0<4*g+ms.length) (i : Fin (4*g+ms.length)) :
    ∃j<4*g+ms.length,
      ((cofiniteConstructionVertexStep g ms last)^[j])
        (cofiniteConstructionBaseIndex g ms last ⟨0,hB⟩) = cofiniteConstructionBaseIndex g ms last i := by
  refine ⟨i.val, i.isLt, ?_⟩
  rw [cofiniteConstructionBaseIndex_iterate]
  have hrot : ((finRotate _)^[i.val]) ⟨0,hB⟩=i := by
    let cofiniteBaseCountNeZero : NeZero (4*g+ms.length) := ⟨by omega⟩
    rw [← finCycle_eq_finRotate_iterate (k:=i)]
    change (0:Fin (4*g+ms.length))+i=i
    exact zero_add i
  exact congrArg (cofiniteConstructionBaseIndex g ms last) hrot

theorem cofiniteConstructionMarkBaseNat_angle (α : ℝ) (ms : List ℕ) (i : ℕ) :
    (cofiniteConstructionMarkAngles α ms).getD (cofiniteConstructionMarkBaseNat ms i) α=α := by
  induction ms generalizing i with
  | nil => simp [cofiniteConstructionMarkAngles]
  | cons m ms ih =>
    cases i with
    | zero => by_cases hm:m=2 <;> simp [cofiniteConstructionMarkBaseNat,cofiniteConstructionMarkAngles,hm]
    | succ i =>
      rw [cofiniteConstructionMarkBaseNat]
      by_cases hm:m=2
      · rw [ite_eq_left hm, cofiniteConstructionMarkAngles, ite_eq_left hm,
          show 1+cofiniteConstructionMarkBaseNat ms i=cofiniteConstructionMarkBaseNat ms i+1 by omega,
          cofiniteConstruction_getD_cons]
        exact ih i
      · rw [ite_eq_right hm, cofiniteConstructionMarkAngles, ite_eq_right hm,
          show 2+cofiniteConstructionMarkBaseNat ms i=(cofiniteConstructionMarkBaseNat ms i+1)+1 by omega,
          cofiniteConstruction_getD_cons, cofiniteConstruction_getD_cons]
        exact ih i

theorem cofiniteConstructionBaseNat_angle (α : ℝ) (g : ℕ) (ms : List ℕ) (i : ℕ) :
    (cofiniteConstructionSideAngles α g ms).getD (cofiniteConstructionBaseNat g ms i) α=α := by
  induction g generalizing i with
  | zero => exact cofiniteConstructionMarkBaseNat_angle α ms i
  | succ g ih =>
    by_cases hi:i<4
    · interval_cases i <;>
        simp [cofiniteConstructionSideAngles_handle,cofiniteConstructionBaseNat,cofiniteConstructionHandleBaseNat]
    · obtain ⟨j,rfl⟩ : ∃j,i=4+j := ⟨i-4,by omega⟩
      rw [cofiniteConstructionBaseNat,ite_eq_right (by omega),show 4+j-4=j by omega,
        cofiniteConstructionSideAngles_handle,
        show 4+cofiniteConstructionBaseNat g ms j=cofiniteConstructionBaseNat g ms j+4 by omega,
        cofiniteConstruction_getD_four]
      exact ih j

theorem cofiniteConstructionBaseIndex_angle (g : ℕ) (ms : List ℕ) (last : ℕ)
    (i : Fin (4*g+ms.length)) :
    (cofiniteConstructionAngles g ms last)[cofiniteConstructionBaseIndex g ms last i] =
      cofiniteConstructionBaseAngle g ms last := by
  let α:=cofiniteConstructionBaseAngle g ms last
  have h : (cofiniteConstructionAngles g ms last).getD
      (cofiniteConstructionBaseIndex g ms last i).val α=α := by
    rw [cofiniteConstructionBaseIndex_val]
    simpa only [cofiniteConstructionAngles_eq_sideAngles] using
      cofiniteConstructionBaseNat_angle α g ms i.val
  simpa only [List.getD_eq_getElem _ α (cofiniteConstructionBaseIndex g ms last i).isLt,
    Fin.getElem_fin] using h

theorem cofiniteConstructionMarkOuterNat_bound (α : ℝ) (ms : List ℕ) (i : ℕ)
    (hi:i<ms.length) (hm:ms.getD i 2≠2) :
    cofiniteConstructionMarkBaseNat ms i+1 < (cofiniteConstructionMarkAngles α ms).length := by
  induction ms generalizing i with
  | nil => simp at hi
  | cons m ms ih =>
    cases i with
    | zero =>
      have hm':m≠2:=hm
      simp [cofiniteConstructionMarkBaseNat,cofiniteConstructionMarkAngles,hm']
    | succ i =>
      have hi':i<ms.length:=by simpa using hi
      have hm':ms.getD i 2≠2:=hm
      have hh:=ih i hi' hm'
      by_cases hm2:m=2 <;>
        simp only [cofiniteConstructionMarkBaseNat,cofiniteConstructionMarkAngles,hm2,
          ite_true,ite_false,List.length_cons] <;> omega

theorem cofiniteConstructionMarkOuterNat_fixed (ms : List ℕ) (i : ℕ)
    (hi:i<ms.length) (hm:ms.getD i 2≠2) :
    cofiniteConstructionMarkPairNat ms (cofiniteConstructionMarkBaseNat ms i+1)+1=
      cofiniteConstructionMarkBaseNat ms i+1 := by
  induction ms generalizing i with
  | nil => simp at hi
  | cons m ms ih =>
    cases i with
    | zero =>
      have hm':m≠2:=hm
      simp [cofiniteConstructionMarkBaseNat,cofiniteConstructionMarkPairNat,hm']
    | succ i =>
      have hi':i<ms.length:=by simpa using hi
      have hm':ms.getD i 2≠2:=hm
      rw [cofiniteConstructionMarkBaseNat,
        show (if m=2 then 1 else 2)+cofiniteConstructionMarkBaseNat ms i+1=
          (if m=2 then 1 else 2)+(cofiniteConstructionMarkBaseNat ms i+1) by omega,
        cofiniteConstructionMarkPairNat_shift]
      have hh:=ih i hi' hm'
      omega

theorem cofiniteConstructionPairNat_handle_prefix (g : ℕ) (ms : List ℕ) (i : ℕ) :
    cofiniteConstructionPairNat g ms (4*g+i)=4*g+cofiniteConstructionMarkPairNat ms i := by
  induction g with
  | zero => simp only [Nat.mul_zero,Nat.zero_add,cofiniteConstructionPairNat]
  | succ g ih =>
    rw [show 4*(g+1)+i=4+(4*g+i) by omega, cofiniteConstructionPairNat_shift, ih]
    omega

def cofiniteConstructionOuterIndex (g : ℕ) (ms : List ℕ) (last : ℕ)
    (i : {j:Fin ms.length // ms[j]≠2}) : Fin (cofiniteConstructionAngles g ms last).length :=
  ⟨4*g+cofiniteConstructionMarkBaseNat ms i.val.val+1, by
    have hm : ms.getD i.val.val 2≠2 := by
      simpa only [List.getD_eq_getElem _ 2 i.val.isLt,Fin.getElem_fin] using i.property
    have hb := cofiniteConstructionMarkOuterNat_bound (cofiniteConstructionBaseAngle g ms last)
      ms i.val.val i.val.isLt hm
    have hlen:=congrArg List.length (cofiniteConstructionAngles_eq_sideAngles g ms last)
    simp only [cofiniteConstructionSideAngles,List.length_append,List.length_replicate] at hlen
    omega⟩

theorem cofiniteConstructionOuterIndex_injective (g : ℕ) (ms : List ℕ) (last : ℕ) :
    Function.Injective (cofiniteConstructionOuterIndex g ms last) := by
  intro i j hij
  have he:=congrArg Fin.val hij
  change 4*g+cofiniteConstructionMarkBaseNat ms i.val.val+1=
    4*g+cofiniteConstructionMarkBaseNat ms j.val.val+1 at he
  have hp:cofiniteConstructionMarkBaseNat ms i.val.val=cofiniteConstructionMarkBaseNat ms j.val.val:=by omega
  exact Subtype.ext (Fin.ext (cofiniteConstructionMarkBaseNat_injective ms hp))

theorem cofiniteConstructionOuterIndex_fixed (g : ℕ) (ms : List ℕ) (last : ℕ)
    (i : {j:Fin ms.length // ms[j]≠2}) :
    cofiniteConstructionVertexStep g ms last (cofiniteConstructionOuterIndex g ms last i)=
      cofiniteConstructionOuterIndex g ms last i := by
  have hm : ms.getD i.val.val 2≠2 := by
    simpa only [List.getD_eq_getElem _ 2 i.val.isLt,Fin.getElem_fin] using i.property
  have hf:=cofiniteConstructionMarkOuterNat_fixed ms i.val.val i.val.isLt hm
  have hrot:=cofiniteConstruction_finRotate_val
    (cofiniteConstructionPairing g ms last (cofiniteConstructionOuterIndex g ms last i))
  rw [cofiniteConstructionPairing_val] at hrot
  apply Fin.ext
  change (finRotate _ (cofiniteConstructionPairing g ms last (cofiniteConstructionOuterIndex g ms last i))).val=_
  rw [hrot]
  change (if cofiniteConstructionPairNat g ms
      (4*g+cofiniteConstructionMarkBaseNat ms i.val.val+1)+1=(cofiniteConstructionAngles g ms last).length
    then 0 else cofiniteConstructionPairNat g ms (4*g+cofiniteConstructionMarkBaseNat ms i.val.val+1)+1)=
      4*g+cofiniteConstructionMarkBaseNat ms i.val.val+1
  have hp:cofiniteConstructionPairNat g ms (4*g+cofiniteConstructionMarkBaseNat ms i.val.val+1)+1=
      4*g+cofiniteConstructionMarkBaseNat ms i.val.val+1 := by
    rw [show 4*g+cofiniteConstructionMarkBaseNat ms i.val.val+1=
      4*g+(cofiniteConstructionMarkBaseNat ms i.val.val+1) by omega,
      cofiniteConstructionPairNat_handle_prefix]
    omega
  rw [hp,ite_eq_right (by have hh:=(cofiniteConstructionOuterIndex g ms last i).isLt;exact ne_of_lt hh)]

theorem cofiniteConstructionBaseIndex_ne_outer (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB:2≤4*g+ms.length) (i:Fin (4*g+ms.length)) (j:{j:Fin ms.length // ms[j]≠2}) :
    cofiniteConstructionBaseIndex g ms last i ≠ cofiniteConstructionOuterIndex g ms last j := by
  intro he
  have hfix : cofiniteConstructionBaseIndex g ms last (finRotate _ i)=cofiniteConstructionBaseIndex g ms last i := by
    rw [cofiniteConstructionBaseIndex_next, he]
    exact cofiniteConstructionOuterIndex_fixed g ms last j
  have hrot := cofiniteConstructionBaseIndex_injective g ms last hfix
  have hv := cofiniteConstruction_finRotate_val i
  rw [hrot] at hv
  have hi:=i.isLt
  split_ifs at hv <;> omega

theorem cofiniteConstructionMarkAngles_length (α:ℝ) (ms:List ℕ) :
    (cofiniteConstructionMarkAngles α ms).length = ms.length+
      (ms.map (fun m=>if m≠2 then 1 else 0)).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    by_cases hm:m=2 <;>
      simp only [cofiniteConstructionMarkAngles,hm,ite_true,ite_false,List.length_cons,
        List.map_cons,List.sum_cons,ih,ne_eq,not_true_eq_false,not_false_eq_true] <;> omega

theorem cofiniteConstructionOuterIndex_card (ms:List ℕ) :
    Fintype.card {j:Fin ms.length // ms[j]≠2}=(ms.map (fun m=>if m≠2 then 1 else 0)).sum := by
  classical
  have hlist := congrArg (List.map (fun m:ℕ=>if m≠2 then (1:ℕ) else 0)) (List.ofFn_getElem (xs:=ms))
  simp only [List.map_ofFn,Function.comp_def] at hlist
  have hsum:=congrArg List.sum hlist
  rw [List.sum_ofFn] at hsum
  calc
    Fintype.card {j:Fin ms.length // ms[j]≠2}=
        ∑j:Fin ms.length,if ms[j]≠2 then 1 else 0 := by
      rw [Fintype.card_subtype]
      exact (Finset.sum_boole (fun j:Fin ms.length=>ms[j]≠2) Finset.univ).symm
    _=_:=hsum

/-- Every original corner has exactly one independent base or outer label. -/
def cofiniteConstructionCornerLabelEquiv (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hB:2≤4*g+ms.length) :
    Fin (4*g+ms.length) ⊕ {j:Fin ms.length // ms[j]≠2} ≃
      Fin (cofiniteConstructionAngles g ms last).length := by
  classical
  let f:=Sum.elim (cofiniteConstructionBaseIndex g ms last) (cofiniteConstructionOuterIndex g ms last)
  have hf:Function.Injective f :=
    (cofiniteConstructionBaseIndex_injective g ms last).sumElim
      (cofiniteConstructionOuterIndex_injective g ms last)
      (cofiniteConstructionBaseIndex_ne_outer g ms last hB)
  have hc:Fintype.card (Fin (4*g+ms.length) ⊕ {j:Fin ms.length // ms[j]≠2})=
      Fintype.card (Fin (cofiniteConstructionAngles g ms last).length) := by
    rw [Fintype.card_sum,Fintype.card_fin,Fintype.card_fin,cofiniteConstructionOuterIndex_card,
      cofiniteConstructionAngles_eq_sideAngles]
    simp only [cofiniteConstructionSideAngles,List.length_append,List.length_replicate,
      cofiniteConstructionMarkAngles_length]
    omega
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hc⟩)

theorem cofiniteConstructionCornerLabelEquiv_base (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hB:2≤4*g+ms.length) (i:Fin (4*g+ms.length)) :
    cofiniteConstructionCornerLabelEquiv g ms last hB (Sum.inl i)=cofiniteConstructionBaseIndex g ms last i := rfl

theorem cofiniteConstructionCornerLabelEquiv_outer (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hB:2≤4*g+ms.length) (i:{j:Fin ms.length // ms[j]≠2}) :
    cofiniteConstructionCornerLabelEquiv g ms last hB (Sum.inr i)=cofiniteConstructionOuterIndex g ms last i := rfl

/-- The full natural corner permutation has one labelled base cycle and exactly
the separately labelled outer singleton cycles, even when numerical angles coincide. -/
theorem cofiniteConstructionCornerLabelEquiv_step (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hB:2≤4*g+ms.length)
    (i:Fin (4*g+ms.length) ⊕ {j:Fin ms.length // ms[j]≠2}) :
    cofiniteConstructionVertexStep g ms last (cofiniteConstructionCornerLabelEquiv g ms last hB i)=
      cofiniteConstructionCornerLabelEquiv g ms last hB
        (Sum.map (finRotate _) id i) := by
  cases i with
  | inl i => exact (cofiniteConstructionBaseIndex_next g ms last i).symm
  | inr j => exact cofiniteConstructionOuterIndex_fixed g ms last j


theorem cofiniteConstructionMarkOuterNat_angle (α:ℝ) (ms:List ℕ) (i:ℕ)
    (hi:i<ms.length) (hm:ms.getD i 2≠2) :
    (cofiniteConstructionMarkAngles α ms).getD (cofiniteConstructionMarkBaseNat ms i+1) α =
      cofiniteConstructionConeAngle (ms.getD i 2) := by
  induction ms generalizing i with
  | nil => simp at hi
  | cons m ms ih =>
    cases i with
    | zero =>
      have hm':m≠2:=hm
      simp [cofiniteConstructionMarkBaseNat,cofiniteConstructionMarkAngles,hm']
    | succ i =>
      have hi':i<ms.length:=by simpa using hi
      have hm':ms.getD i 2≠2:=hm
      rw [cofiniteConstructionMarkBaseNat]
      by_cases hm2:m=2
      · rw [ite_eq_left hm2,cofiniteConstructionMarkAngles,ite_eq_left hm2,
          show 1+cofiniteConstructionMarkBaseNat ms i+1=(cofiniteConstructionMarkBaseNat ms i+1)+1 by omega,
          cofiniteConstruction_getD_cons]
        exact ih i hi' hm'
      · rw [ite_eq_right hm2,cofiniteConstructionMarkAngles,ite_eq_right hm2,
          show 2+cofiniteConstructionMarkBaseNat ms i+1=((cofiniteConstructionMarkBaseNat ms i+1)+1)+1 by omega,
          cofiniteConstruction_getD_cons,cofiniteConstruction_getD_cons]
        exact ih i hi' hm'

theorem cofiniteConstructionSideAngles_mark_getD (α:ℝ) (g:ℕ) (ms:List ℕ) (i:ℕ) :
    (cofiniteConstructionSideAngles α g ms).getD (4*g+i) α =
      (cofiniteConstructionMarkAngles α ms).getD i α := by
  induction g with
  | zero => simp only [Nat.mul_zero,Nat.zero_add,cofiniteConstructionSideAngles,List.replicate_zero,List.nil_append]
  | succ g ih =>
    rw [show 4*(g+1)+i=(4*g+i)+4 by omega,cofiniteConstructionSideAngles_handle,
      cofiniteConstruction_getD_four,ih]

theorem cofiniteConstructionOuterIndex_angle (g:ℕ) (ms:List ℕ) (last:ℕ)
    (i:{j:Fin ms.length // ms[j]≠2}) :
    (cofiniteConstructionAngles g ms last)[cofiniteConstructionOuterIndex g ms last i] =
      cofiniteConstructionConeAngle ms[i.val] := by
  let α:=cofiniteConstructionBaseAngle g ms last
  have hm:ms.getD i.val.val 2≠2:=by
    simpa only [List.getD_eq_getElem _ 2 i.val.isLt,Fin.getElem_fin] using i.property
  have h : (cofiniteConstructionAngles g ms last).getD
      (cofiniteConstructionOuterIndex g ms last i).val α=cofiniteConstructionConeAngle (ms.getD i.val.val 2) := by
    change (cofiniteConstructionAngles g ms last).getD
      (4*g+cofiniteConstructionMarkBaseNat ms i.val.val+1) α=_
    rw [cofiniteConstructionAngles_eq_sideAngles,
      show 4*g+cofiniteConstructionMarkBaseNat ms i.val.val+1=4*g+(cofiniteConstructionMarkBaseNat ms i.val.val+1) by omega,
      cofiniteConstructionSideAngles_mark_getD]
    exact cofiniteConstructionMarkOuterNat_angle α ms i.val.val i.val.isLt hm
  simpa only [List.getD_eq_getElem _ α (cofiniteConstructionOuterIndex g ms last i).isLt,
    List.getD_eq_getElem _ 2 i.val.isLt,Fin.getElem_fin] using h


open Fin.NatCast in
/-- The base orbit closes after exactly the prescribed number of labelled base marks. -/
theorem cofiniteConstructionBaseIndex_full_turn (g:ℕ) (ms:List ℕ) (last:ℕ)
    (i:Fin (4*g+ms.length)) :
    ((cofiniteConstructionVertexStep g ms last)^[4*g+ms.length])
      (cofiniteConstructionBaseIndex g ms last i)=cofiniteConstructionBaseIndex g ms last i := by
  let cofiniteBaseCountNeZero : NeZero (4*g+ms.length) := i.neZero
  have hrot (j:ℕ) : ((finRotate (4*g+ms.length))^[j]) i=i+(j:Fin (4*g+ms.length)) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply',ih,finRotate_apply]
      simp only [Nat.cast_add,Nat.cast_one,add_assoc]
  rw [cofiniteConstructionBaseIndex_iterate,hrot,Fin.natCast_self,add_zero]

theorem cofiniteConstructionBaseIndex_no_early_return (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hB:0<4*g+ms.length) (j:ℕ) (hj:j<4*g+ms.length) :
    ((cofiniteConstructionVertexStep g ms last)^[j])
      (cofiniteConstructionBaseIndex g ms last ⟨0,hB⟩)=
        cofiniteConstructionBaseIndex g ms last ⟨0,hB⟩ ↔ j=0 := by
  rw [cofiniteConstructionBaseIndex_iterate]
  constructor
  · intro he
    have hh:=cofiniteConstructionBaseIndex_injective g ms last he
    let cofiniteBaseCountNeZero : NeZero (4*g+ms.length) := ⟨by omega⟩
    rw [←finCycle_eq_finRotate_iterate (k:=⟨j,hj⟩)] at hh
    change (0:Fin (4*g+ms.length))+⟨j,hj⟩=0 at hh
    rw [zero_add] at hh
    exact congrArg Fin.val hh
  · rintro rfl
    rfl


/-- The angle sum of the actual base cycle is the prescribed final cone angle. -/
theorem cofiniteConstructionBaseIndex_angle_sum (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hB:0<4*g+ms.length) :
    (∑i:Fin (4*g+ms.length),
      (cofiniteConstructionAngles g ms last)[cofiniteConstructionBaseIndex g ms last i]) =
        cofiniteConstructionConeAngle last := by
  simp only [cofiniteConstructionBaseIndex_angle,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,cofiniteConstructionBaseAngle]
  have hB':((4*g+ms.length:ℕ):ℝ)≠0:=by exact_mod_cast (ne_of_gt hB)
  field_simp

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
/-- Every actual finite-signature corner has its explicit complete angular
period. Base labels and outer labels remain distinct, including equal angles. -/
theorem cofiniteConstruction_finite_angular_periods (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) :
    ∀i:Fin (cofiniteConstructionAngles g ms last).length,∃N:ℕ,3≤N ∧
      ((cofiniteConstructionVertexStep g ms last)^[N]) i=i ∧
      (cofiniteConstructionAngles g ms last)[i]=2*Real.pi/(N:ℝ) := by
  let B:=4*g+ms.length
  let τ:=cofiniteConstructionVertexStep g ms last
  have hB:2≤B:=cofiniteConstruction_base_count g ms last hdef
  intro i
  obtain ⟨label,rfl⟩:=(cofiniteConstructionCornerLabelEquiv g ms last hB).surjective i
  cases label with
  | inl a =>
    rw [cofiniteConstructionCornerLabelEquiv_base]
    have hN:4≤B*last:=by simpa using Nat.mul_le_mul hB hlast
    refine ⟨B*last,by omega,?_,?_⟩
    · have hBase:τ^[B] (cofiniteConstructionBaseIndex g ms last a)=cofiniteConstructionBaseIndex g ms last a:=
        cofiniteConstructionBaseIndex_full_turn g ms last a
      have hMany:∀k:ℕ,τ^[B*k] (cofiniteConstructionBaseIndex g ms last a)=
          cofiniteConstructionBaseIndex g ms last a:=by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [Nat.mul_succ,Function.iterate_add_apply,hBase,ih]
      exact hMany last
    · rw [cofiniteConstructionBaseIndex_angle]
      dsimp only [cofiniteConstructionBaseAngle,cofiniteConstructionConeAngle,B]
      push_cast
      rw [div_div]
      congr 1
      ring
  | inr j =>
    rw [cofiniteConstructionCornerLabelEquiv_outer]
    have hm:2≤ms[j.val]:=hms _ (List.getElem_mem j.val.isLt)
    have hm3:3≤ms[j.val]:=by have:=j.property;omega
    refine ⟨ms[j.val],hm3,?_,?_⟩
    · have hFix:τ (cofiniteConstructionOuterIndex g ms last j)=
          cofiniteConstructionOuterIndex g ms last j:=cofiniteConstructionOuterIndex_fixed g ms last j
      have hMany:∀k:ℕ,τ^[k] (cofiniteConstructionOuterIndex g ms last j)=
          cofiniteConstructionOuterIndex g ms last j:=by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply,hFix,ih]
      exact hMany _
    · rw [cofiniteConstructionOuterIndex_angle]
      rfl

theorem cofiniteConstruction_angles_pos_finite (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) :
    ∀i:Fin (cofiniteConstructionAngles g ms last).length,
      0<(cofiniteConstructionAngles g ms last)[i] := by
  intro i
  obtain ⟨N,hN,_hcycle,hAngle⟩:=cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef i
  rw [hAngle]
  exact div_pos (by positivity) (by exact_mod_cast (by omega:0<N))

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- Strictly positive original prescribed angles give actual finite vertices. -/
theorem cofiniteTangential_finite_of_positive_angles {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (hpos:∀i,0<θ i) :
    ∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1 := by
  intro i
  by_contra hn
  have he:‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖=1:=
    le_antisymm ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i).norm_le_one (le_of_not_gt hn)
  have ha:θ i=0:=by
    rw [←_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle θ d hθ hd hb i,
      _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.angle_of_ideal _ i he]
  exact (ne_of_gt (hpos i)) ha

/-- The literal prescribed finite-signature polygon and pairing satisfy the
complete actual canonical cycles; neither charts nor cycles are inputs. -/
theorem cofiniteConstruction_finite_canonical_cycles (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i=> (cofiniteConstructionAngles g ms last)[i]) d=Real.pi) :
    let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=
      fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]
    let hθ:∀i:Fin (cofiniteConstructionAngles g ms last).length,
        θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
      (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
    let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
      (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
    let ρ:=cofiniteConstructionPairing g ms last
    _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonCanonicalCycleConditions (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf
      (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ
        (cofiniteConstructionPairing_involutive g ms last)
        (cofiniteConstructionPairing_angle_profile g ms last)) := by
  dsimp only
  apply cofiniteTangential_canonical_cycle_conditions
  intro i
  exact cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef i

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual pairing mirror is a genuine diameter reflection, including
its entire finite and ideal extension. -/
theorem cofiniteTangentMirror_genuine_line {n:ℕ} (θ:Fin n→ℝ) (d:ℝ) (i j:Fin n) :
    ∃L:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L=
        triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) ∧
      UpperHalfPlane.I∈L.carrier ∧
      ∀p:𝕔𝔻,L.toDiscLine.closedReflectionIsometry.closedMap p=
        cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j) p := by
  let t:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (i.val+1)+_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (j.val+1)
  let u:=Circle.exp (t/2)
  obtain ⟨L,hL⟩:=regular_unit_mirror_exists u
  have hu:u^2=Circle.exp t:=by
    dsimp only [u]
    rw [←Circle.exp_natCast_mul]
    congr 1
    ring
  have hM:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L=
      triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j):=by
    rw [hL,hu]
    rfl
  have hI:UpperHalfPlane.I∈L.carrier:=by
    apply (L.reflection_fixed_iff UpperHalfPlane.I).mp
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L UpperHalfPlane.I=UpperHalfPlane.I
    rw [hM]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (cofiniteTangentMirror θ d i j)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I))=UpperHalfPlane.I
    have hz:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=0:=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero])
    rw [hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap_zero,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero]
  let :T2Space 𝕔𝔻:=Complex.UnitClosedDisc.isEmbedding_coe.t2Space
  have hClosed:(fun p:𝕔𝔻=>L.toDiscLine.closedReflectionIsometry.closedMap p)=
      fun p:𝕔𝔻=>cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j) p:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.denseRange_discToClosedModel.equalizer
    · exact L.toDiscLine.closedReflectionIsometry.closedMap.continuous
    · exact (cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)).continuous
    · funext z
      simp only [Function.comp_apply]
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes]
      have hp:=congrArg (fun f:ℍ≃ᵢℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))) hM
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (L.reflection (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (cofiniteTangentMirror θ d i j)
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)))) at hp
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] at hp
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
          (L.toDiscLine.toHalfPlane.reflection (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)))=_
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane,hp]
      rfl
  exact ⟨L,hM,hI,congrFun hClosed⟩

theorem cofiniteTangential_zero_vertex_ideal {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (i:Fin n) (hzero:θ i=0) :
    ‖(_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i:ℂ)‖=1 := by
  rw [←_root_.LowDimensionalTopology.Geometry.Polygon.norm_closedKleinCoordinate_eq_one_iff,_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_coordinate,
    norm_smul,Real.norm_eq_abs,abs_of_pos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_pos (hθ i) hd),
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm,mul_one,_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_eq_one_iff (hθ i) hd]
  exact hzero

/-- The positive common incircle radius keeps every genuine side support
away from its center. -/
theorem cofiniteTangential_side_avoids_origin {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) :
    UpperHalfPlane.I∉(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i).carrier := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  have hline:Q.geodesicSide i=S.supportLine i:=by
    apply (Q.geodesicSide i).eq_of_two_closed_points (S.supportLine i)
      (Q.vertices_injective.ne (Q.next_ne_self i).symm)
      (Q.geodesicSide_endpoints i).1 (Q.geodesicSide_endpoints i).2
    · exact (S.incident_mem_support i).1
    · exact (S.incident_mem_support i).2
  intro hI
  have hz:(0:𝔻)∈(Q.geodesicSide i).carrier:=by
    apply ((Q.geodesicSide i).mem_carrier 0).mpr
    change UpperHalfPlane.I∈(Q.geodesicSide i).toHalfPlane.carrier at hI
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero] using hI
  have hc:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0:𝔻)∈(S.supportLine i).closedCarrier:=by
    rw [←hline]
    exact ((Q.geodesicSide i).closedCarrier_mem_interior_iff 0).mpr hz
  have he:inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0:𝔻)))=S.offsets i:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_closed_equation_iff _ _ _ _ _).mp hc
  have hk:_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0:𝔻)=0:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula 0=0
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,mul_zero]
  have ht:(0:ℝ)=Real.tanh d:=by
    change inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0:𝔻)))=Real.tanh d at he
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,hk,inner_zero_right] using he
  exact (ne_of_gt (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hd)) ht.symm


end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set
  Filter
  Topology
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- Every true side germ is its actual inward component, with the same
physical incircle center serving as the reference point for all sides. -/
theorem cofiniteTangential_nonvertex_incircle_component_germ {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (i:Fin n) (x:ℍ) (hx:x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i)
    (hv:x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf)) :
    ∀ᶠw in 𝓝 x,
      w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf).carrier ↔
        w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i) UpperHalfPlane.I := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  have hQ:Q.IsConvex:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb
  have ha:∀j,Q.angle j<Real.pi:=by
    intro j
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]
    exact (hθ j).2
  let B:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha
  let N:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i
  have hII:UpperHalfPlane.I∈P.interior:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I∈Q.interior
    have hz:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=0:=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero])
    rw [hz]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_origin_mem θ d hθ hd hb
  have hIle:inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate UpperHalfPlane.I)≤B.offsets i:=
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_carrier_support_iff Q hQ ha hf UpperHalfPlane.I).mp
      (P.interior_subset_carrier hII) i
  have hIlt:inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate UpperHalfPlane.I)<B.offsets i:=by
    apply lt_of_le_of_ne hIle
    intro he
    exact cofiniteTangential_side_avoids_origin θ d hθ hd hb i
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha i UpperHalfPlane.I).mpr he)
  have hm:B.normals i≠0:=by
    intro he
    have hh:=B.normal_norm i
    rw [he,norm_zero] at hh
    norm_num at hh
  have hCut:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N UpperHalfPlane.I=
      {z:ℍ|inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤B.offsets i}:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlane_eq_le N (B.normals i) (B.offsets i) hm
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha i) UpperHalfPlane.I hIlt
  obtain ⟨r,hr,hG⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_nonvertex_support_germ Q hQ ha hf hx hv
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨r,hr,?_⟩
  intro w hw
  rw [hCut]
  exact hG w hw

/-- The actual radial mirror carries the entire true side-support line to
its paired support line; this asserts no symmetry of the polygon. -/
theorem cofiniteTangentMirror_native_line_image {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (i j:Fin n) (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j) :
    triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) ''
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i).carrier=
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) j).carrier := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
  let N:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i
  let L:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q j
  have hc (z:ℍ):M (N.reflection (M.symm z))=L.reflection z:=
    congrArg (fun f:ℍ≃ᵢℍ=>f z) (cofiniteTangentMirror_line_conjugation θ d hθ hd hb i j hl hr)
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    apply (L.reflection_fixed_iff (M w)).mp
    have hh:=hc (M w)
    rw [M.symm_apply_apply,(N.reflection_fixed_iff w).mpr hw] at hh
    exact hh.symm
  · intro hz
    refine ⟨M.symm z,?_,M.apply_symm_apply z⟩
    apply (N.reflection_fixed_iff (M.symm z)).mp
    apply M.injective
    rw [M.apply_symm_apply]
    exact (hc z).trans ((L.reflection_fixed_iff z).mpr hz)

/-- The true common-center inward half-planes are transported globally by
the actual mirror, independently of the remaining polygon supports. -/
theorem cofiniteTangentMirror_native_inward_iff {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (i j:Fin n) (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j) (z:ℍ) :
    triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) z∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) j) UpperHalfPlane.I ↔
    z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i) UpperHalfPlane.I := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
  obtain ⟨L,hL,hLI,_hClosed⟩:=cofiniteTangentMirror_genuine_line θ d i j
  have hMI:M UpperHalfPlane.I=UpperHalfPlane.I:=by
    change triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) UpperHalfPlane.I=UpperHalfPlane.I
    rw [←hL]
    exact (L.reflection_fixed_iff _).mpr hLI
  have he:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_image_closed_halfPlane M (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q j)
    (cofiniteTangentMirror_native_line_image θ d hθ hd hb i j hl hr) UpperHalfPlane.I
    (cofiniteTangential_side_avoids_origin θ d hθ hd hb i)
  rw [hMI] at he
  rw [←he]
  exact M.injective.mem_set_image

/-- The unchanged actual pairing satisfies the original opposite-side
relative-neighborhood convention at every nonvertex point of every side. -/
theorem cofiniteTangential_opposite_side_neighborhoods {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (x:ℍ)
    (hx:x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i)
    (hv:x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf)) :
    (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).OppositeSideNeighborhoods
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i) x := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let S₀:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePairing Q hf
  let s:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i (ρ i))
  let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i)
  let :IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  let :IsIsometricSMul S₀.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hr:θ (finRotate n i)=θ (ρ i):=cofiniteTangentialPairing_other_angle θ ρ hρ hθρ i
  have hRx:R x=x:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).reflection_fixed_iff x |>.mpr
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hx)
  have hAx:S.element s x=M x:=by
    rw [cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ i]
    change M (R x)=M x
    rw [hRx]
  have hy:M x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q (ρ i):=by
    rw [←cofiniteTangentMirror_native_side_image θ d hθ hd hb i (ρ i) (hθρ i) hr]
    exact mem_image_of_mem M hx
  have hyv:M x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf):=by
    have hh:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_pairing_nonvertex Q hf S i hx hv
    rwa [hAx] at hh
  have hi:=cofiniteTangential_nonvertex_incircle_component_germ θ d hθ hd hb hf i x hx hv
  have hj:=cofiniteTangential_nonvertex_incircle_component_germ θ d hθ hd hb hf (ρ i) (M x) hy hyv
  have hj':∀ᶠz in 𝓝 x,
      M z∈P.carrier ↔M z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q (ρ i)) UpperHalfPlane.I:=
    (M.continuous.tendsto x).eventually hj
  have hLocal:∀ᶠz in 𝓝 x,M z∈P.carrier ↔z∈P.carrier:=by
    filter_upwards [hi,hj'] with z hiz hjz
    exact hjz.trans ((cofiniteTangentMirror_native_inward_iff θ d hθ hd hb i (ρ i) (hθρ i) hr z).trans hiz.symm)
  have hRt:Tendsto R (𝓝 x) (𝓝 x):=by
    simpa only [hRx] using R.continuous.tendsto x
  have hReflect:∀ᶠz in 𝓝 x,M (R z)∈P.carrier ↔R z∈P.carrier:=hRt.eventually hLocal
  have ha:∀j,Q.angle j<Real.pi:=by
    intro j
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]
    exact (hθ j).2
  let p:P.Point:=⟨x,P.side_subset_carrier s hx⟩
  obtain ⟨r,hstar⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_nonvertex_paired_side Q
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb) ha hf p i hx hv
  have hOld:∀ᶠz in 𝓝 x,z∈P.carrier ∨R z∈P.carrier:=by
    have hh:=(S₀.oppositeSideNeighborhoods_iff s x).mp (hstar.oppositeSideNeighborhoods S₀)
    change ∀ᶠz in 𝓝 x,z∈P.carrier ∨S₀.element s z∈P.carrier at hh
    have he:S₀.element s=R:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePairing_element Q hf i
    simpa only [he] using hh
  apply (S.oppositeSideNeighborhoods_iff s x).mpr
  filter_upwards [hOld,hReflect] with z hz hRefl
  change z∈P.carrier ∨S.element s z∈P.carrier
  rcases hz with hz|hz
  · exact Or.inl hz
  · apply Or.inr
    rw [cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ i]
    exact hRefl.mpr hz


/-- The original universal side convention holds for every actual original
side label of the unchanged finite specialization. -/
theorem cofiniteTangential_all_opposite_side_neighborhoods {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
    ∀s:(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).Side,∀x∈s.val,
      x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf) → S.OppositeSideNeighborhoods s x := by
  dsimp only
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  intro s
  obtain ⟨i,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective s
  intro x hx hv
  exact cofiniteTangential_opposite_side_neighborhoods θ d hθ hd hb hf ρ hρ hθρ i x hx hv

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- Genuine prescribed angular periods for the actual positive common-incircle
pairing imply actual discreteness and the literal original fundamental domain. -/
theorem cofiniteTangential_finite_poincare {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) :
    let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
    DiscreteTopology S.Generated ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  apply _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_poincare Q hf S
  · intro i x hx hv
    exact cofiniteTangential_opposite_side_neighborhoods θ d hθ hd hb hf ρ hρ hθρ i x hx hv
  · exact cofiniteTangential_canonical_cycle_conditions θ d hθ hd hb hf ρ hρ hθρ hPeriod

/-- Every actual finite admissible signature construction produces a genuine
native discrete group and the original cofinite polygon as fundamental domain. -/
theorem cofiniteConstruction_finite_poincare (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i=> (cofiniteConstructionAngles g ms last)[i]) d=Real.pi) :
    let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=
      fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]
    let hθ:∀i:Fin (cofiniteConstructionAngles g ms last).length,
        θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
      (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
    let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
      (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
    let ρ:=cofiniteConstructionPairing g ms last
    let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ
        (cofiniteConstructionPairing_involutive g ms last)
        (cofiniteConstructionPairing_angle_profile g ms last)
    DiscreteTopology S.Generated ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior) := by
  dsimp only
  apply cofiniteTangential_finite_poincare
  intro i
  exact cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef i

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The actual deficit supplies the positive radius used by the literal
construction, rather than an assumed existence of a balanced polygon. -/
theorem cofiniteConstruction_radius_exists (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,m=0∨2≤m) (hlast:last=0∨2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) :
    ∃d:ℝ,0<d ∧_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance
      (fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]) d=Real.pi := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=
    fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]
  apply _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance_exists_positive θ
  · intro i
    exact cofiniteConstruction_angles_mem g ms last hms hlast hdef _ (List.getElem_mem i.isLt)
  · have hB:=cofiniteConstruction_base_count g ms last hdef
    have hangle:=cofiniteConstruction_angles_defect g ms last (by omega)
    have hsum:∑i,θ i=(cofiniteConstructionAngles g ms last).sum:=by
      rw [←List.sum_ofFn]
      apply congrArg List.sum
      exact List.ofFn_getElem
    rw [hsum]
    have hpos:0<2*Real.pi*cofiniteConstructionDeficit g ms last:=by positivity
    linarith only [hangle,hpos]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The actual inward side component is precisely the true global support
cut, selected by the physical common incircle center. -/
theorem cofiniteTangential_inward_support_iff {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1) (i:Fin n) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let B:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb)
      (fun j=>by rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle];exact (hθ j).2)
    ∀z:ℍ,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i) UpperHalfPlane.I ↔
      inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤B.offsets i := by
  dsimp only
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  have hQ:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb
  have ha:∀j,Q.angle j<Real.pi:=by intro j;rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle];exact (hθ j).2
  let B:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha
  have hII:UpperHalfPlane.I∈P.interior:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I∈Q.interior
    have hz:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=0:=by
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    rw [hz]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_origin_mem θ d hθ hd hb
  have hIle:inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate UpperHalfPlane.I)≤B.offsets i:=
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_carrier_support_iff Q hQ ha hf UpperHalfPlane.I).mp
      (P.interior_subset_carrier hII) i
  have hIlt:inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate UpperHalfPlane.I)<B.offsets i:=by
    apply lt_of_le_of_ne hIle
    intro he
    exact cofiniteTangential_side_avoids_origin θ d hθ hd hb i
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha i UpperHalfPlane.I).mpr he)
  have hm:B.normals i≠0:=by
    intro he
    have hh:=B.normal_norm i
    rw [he,norm_zero] at hh
    norm_num at hh
  have hCut:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlane_eq_le (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i) (B.normals i) (B.offsets i) hm
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha i) UpperHalfPlane.I hIlt
  intro z
  exact (Set.ext_iff.mp hCut) z

/-- The literal actual neighboring tile meets the original closed polygon
in exactly the original whole side, with no pre-assumed side identification. -/
theorem cofiniteTangentPairing_carrier_intersection {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (i j:Fin n) (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
    P.carrier∩(cofiniteTangentPairingElement θ d hθ hd hb i j) ⁻¹' P.carrier=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  have hQ:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb
  have ha:∀k,Q.angle k<Real.pi:=by intro k;rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle];exact (hθ k).2
  let B:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha
  let N:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
  have hPcut:∀k:Fin n,P.carrier⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k) UpperHalfPlane.I:=by
    intro k z hz
    apply (cofiniteTangential_inward_support_iff θ d hθ hd hb hf k z).mpr
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_carrier_support_iff Q hQ ha hf z).mp hz k
  ext z
  constructor
  · rintro ⟨hz,hAz⟩
    have hRz:N.reflection z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N UpperHalfPlane.I:=
      (cofiniteTangentMirror_native_inward_iff θ d hθ hd hb i j hl hr _).mp (hPcut j hAz)
    have hcutR:inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (N.reflection z))≤B.offsets i:=
      (cofiniteTangential_inward_support_iff θ d hθ hd hb hf i _).mp hRz
    obtain ⟨σ,hσ,hCut⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_side_signed_support Q hQ ha hf i
    have hpos:0≤σ*N.normalTimeAt z:=(hCut z).mpr
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_carrier_support_iff Q hQ ha hf z).mp hz i)
    have hneg:0≤σ*N.normalTimeAt (N.reflection z):=(hCut _).mpr hcutR
    have hunit:N.normalPairing N=1:=by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalPairing,real_inner_self_eq_norm_sq]
      nlinarith only [N.incenterNormal_lorentz_unit]
    rw [N.normalTimeAt_reflection N z,hunit] at hneg
    have hzero:σ*N.normalTimeAt z=0:=by nlinarith only [hpos,hneg]
    have hline:z∈N.carrier:=(N.normalTimeAt_eq_zero_iff z).mp ((mul_eq_zero.mp hzero).resolve_left hσ)
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_eq_carrier_inter_line Q hQ ha hf i]
    exact ⟨hz,hline⟩
  · intro hz
    have hA:cofiniteTangentPairingElement θ d hθ hd hb i j z∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q j:=by
      rw [←cofiniteTangentPairingElement_side_image θ d hθ hd hb i j hl hr]
      exact mem_image_of_mem _ hz
    exact ⟨P.side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i) hz,
      P.side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf j) hA⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- No actual side element is the identity: its reflection factors have
different true support lines, as witnessed by the physical incircle center. -/
theorem cofiniteTangentPairingElement_ne_one {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (i j:Fin n) :cofiniteTangentPairingElement θ d hθ hd hb i j≠1 := by
  let N:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
  obtain ⟨L,hL,hLI,_hClosed⟩:=cofiniteTangentMirror_genuine_line θ d i j
  have hMI:M UpperHalfPlane.I=UpperHalfPlane.I:=by
    change triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) UpperHalfPlane.I=UpperHalfPlane.I
    rw [←hL]
    exact (L.reflection_fixed_iff _).mpr hLI
  intro he
  have hAi:cofiniteTangentPairingElement θ d hθ hd hb i j UpperHalfPlane.I=UpperHalfPlane.I:=
    congrArg (fun f:ℍ≃ᵢℍ=>f UpperHalfPlane.I) he
  have hNI:N.reflection UpperHalfPlane.I=UpperHalfPlane.I:=by
    apply M.injective
    change cofiniteTangentPairingElement θ d hθ hd hb i j UpperHalfPlane.I=M UpperHalfPlane.I
    exact hAi.trans hMI.symm
  exact cofiniteTangential_side_avoids_origin θ d hθ hd hb i
    ((N.reflection_fixed_iff _).mp hNI)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The true actual canonical state closes after its internally proved
angular period, retaining both the native group index and original label. -/
theorem cofiniteTangentialCanonicalWord_closed {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (N:ℕ) (hN:0<N)
    (hClose:((ρ.trans (finRotate n))^[N]) i=i) (hAngle:θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[N]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
      (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i) := by
  dsimp only
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  have hWord:cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i N=1:=by
    apply Subtype.ext
    rw [cofiniteTangentialCanonicalWord_nativeAngularWalkWord]
    exact cofiniteTangential_finite_word_period θ d hθ hd hb ρ hρ hθρ hf i N hN hClose hAngle
  rw [cofiniteTangentialCanonicalWord_flag_state,hWord]
  change ((1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf (((ρ.trans (finRotate n))^[N]) i)):
    _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S)=(1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)
  rw [hClose]

/-- The literal actual finite angular word lists the entire original glued
fiber, with no presumed stabilizer order or whole-class assertion. -/
theorem cofiniteTangentialCanonicalWord_whole_fiber {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (N:ℕ) (hN:0<N)
    (hClose:((ρ.trans (finRotate n))^[N]) i=i) (hAngle:θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
    S.project ⁻¹' {S.project (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf i)}=
      range (fun j:Fin N=>(cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j.val,
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf (((cofiniteTangentialCanonicalIndex ρ)^[j.val]) i))) := by
  obtain ⟨M,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hN.ne'
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let T:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S
  let a:_root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S:=(1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)
  let C:Fin (M+1)→S.Copy:=fun j=>_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[j.val]) a)
  have hclose:(T^[M+1]) a=a:=
    cofiniteTangentialCanonicalWord_closed θ d hθ hd hb hf ρ hρ hθρ i (M+1) hN hClose hAngle
  have hproject (j:ℕ):S.project (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[j]) a))=
      S.project (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S a):=by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hs:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNaturalVertexStep_side_step Q hf S
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPairing_preserves_vertices Q hf S) ((T^[j]) a)
      have he: S.project (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[j]) a))=
          S.project (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((T^[j+1]) a)):=by
        apply (S.project_eq_iff _ _).mpr
        apply Relation.EqvGen.rel
        apply Or.inr
        simpa only [Function.iterate_succ_apply',T,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep] using hs
      exact he.symm.trans ih
  have hF:S.project ⁻¹' {S.project (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S a)}=range C:=by
    apply S.project_fiber_eq_of_step_closed (range C) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S a) ⟨0,rfl⟩
    · rintro b ⟨j,rfl⟩ c hc
      rcases hc with he|⟨s,hs,hy,hg⟩
      · exact he ▸ mem_range_self j
      · have he:=S.sideMateCopy_eq_of_side_step _ c s hs hy hg
        rw [←he]
        exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexCycle_incidence Q hf S a M hclose j s hs
    · rintro b ⟨j,rfl⟩
      exact (S.project_eq_iff _ _).mp (hproject j.val)
  change S.project ⁻¹' {S.project (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S a)}=_
  rw [hF]
  apply congrArg Set.range
  funext j
  exact cofiniteTangentialCanonicalWord_copy θ d hθ hd hb hf ρ hρ hθρ i j.val

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
local instance tangentialOrderDiscMetric : MetricSpace 𝔻:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric

/-- One actual positive frame family gives the full literal native word
coordinate at every original vertex and every genuine iterate. -/
theorem cofiniteTangentialCanonicalWord_coordinates {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) :
    ∃F:Fin n→Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀i,F i • _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i=UpperHalfPlane.I) ∧
      ∀(i:Fin n)(j:ℕ)(x:ℍ),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val x)=
        circleDiscRotationHom (Circle.exp (-(j:ℝ)*θ i))
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F (((cofiniteTangentialCanonicalIndex ρ)^[j]) i) • x)) := by
  obtain ⟨z,F,hz,hcenter,_hgerm,hFrame⟩:=cofiniteTangential_finite_frames θ d hθ hd hb ρ hρ hθρ hf
  refine ⟨F,?_,?_⟩
  · intro i
    have hzi:z i=Complex.UnitDisc.mk ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ) (hf i):=by
      apply Subtype.ext
      exact (congrArg (fun q:𝕔𝔻=>(q:ℂ)) (hz i)).symm
    change F i • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (Complex.UnitDisc.mk _ (hf i))=UpperHalfPlane.I
    rw [←hzi]
    exact hcenter i
  · intro i j x
    let τ:=cofiniteTangentialCanonicalIndex ρ
    let A:ℕ→(ℍ≃ᵢℍ):=fun k=>cofiniteTangentPairingElement θ d hθ hd hb (τ^[k] i) (ρ (τ^[k] i))
    let G:ℕ→Matrix.SpecialLinearGroup (Fin 2) ℝ:=fun k=>F (τ^[k] i)
    let β:ℕ→ℝ:=fun k=>θ (τ^[k] i)
    have hStep:∀k:ℕ,∀y:ℍ,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G (k+1) • A k y):ℂ)=
        (Circle.exp (β k):ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G k • y):ℂ):=by
      intro k y
      have h:=hFrame (τ^[k] i) (F (τ^[k] i) • y)
      rw [inv_smul_smul] at h
      have hh:=congrArg (fun q:𝔻=>(q:ℂ)) h
      rw [circleDiscRotationHom_apply] at hh
      simpa only [G,A,β,Function.iterate_succ_apply',τ,cofiniteTangentialCanonicalIndex,
        Equiv.trans_apply] using hh
    have hsum:(∑k∈Finset.range j,β k)=(j:ℝ)*θ i:=by
      calc
        _=∑_k∈Finset.range j,θ i:=by
          apply Finset.sum_congr rfl
          intro k _hk
          exact cofiniteTangential_angle_iterate θ ρ hθρ i k
        _=_:=by simp
    rw [cofiniteTangentialCanonicalWord_nativeAngularWalkWord]
    apply Complex.UnitDisc.coe_injective
    have hh:=nativeAngularWalk_coordinate A G β hStep j x
    simpa only [G,Function.iterate_zero,Function.id_def,hsum,neg_mul,
      circleDiscRotationHom_apply] using hh

/-- The base-cycle word has its exact original cone order, rather than an
assumed order attached to an abstract presentation. -/
theorem cofiniteTangentialCanonicalWord_order {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (B m:ℕ) (hB:0<B) (hm:0<m)
    (hReturn:((cofiniteTangentialCanonicalIndex ρ)^[B]) i=i)
    (hAngle:θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod (B*m)) :
    orderOf (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i B)=m := by
  obtain ⟨F,_hCenter,hCoordinate⟩:=cofiniteTangentialCanonicalWord_coordinates θ d hθ hd hb hf ρ hρ hθρ
  let W:ℍ≃ᵢℍ:=(cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i B).val
  let e:ℍ≃ᵢ𝔻:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F i)).trans triangleVertexCayleyIsometry
  have hBθ:(B:ℝ)*θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod m:=by
    rw [hAngle]
    dsimp only [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod]
    have hBr:(B:ℝ)≠0:=by exact_mod_cast hB.ne'
    have hmr:(m:ℝ)≠0:=by exact_mod_cast hm.ne'
    push_cast
    field_simp
  have hconj:nativeDiscConjugation e W=circleDiscRotationHom ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator m)⁻¹):=by
    apply IsometryEquiv.ext
    intro z
    obtain ⟨x,rfl⟩:=e.surjective z
    rw [nativeDiscConjugation_apply]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • W x)=circleDiscRotationHom ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator m)⁻¹)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • x))
    have h:=hCoordinate i B x
    have hneg:-(B:ℝ)*θ i= -_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod m:=by rw [neg_mul,hBθ]
    rw [hReturn,hneg,Circle.exp_neg] at h
    exact h
  have ho:=orderOf_injective (nativeDiscConjugation e) (nativeDiscConjugation_injective e) W
  rw [hconj,orderOf_injective circleDiscRotationHom circleDiscRotationHom_injective,orderOf_inv] at ho
  have hW:orderOf W=m:=ho.symm.trans
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot m hm.ne').eq_orderOf.symm
  rw [←orderOf_injective (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated.subtype
    Subtype.val_injective]
  exact hW

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- Actual periodic original labels give literal repeated blocks of the
original generated-group word, without an imposed presentation relation. -/
theorem cofiniteTangentialCanonicalWord_period_blocks {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (B:ℕ)
    (hReturn:((cofiniteTangentialCanonicalIndex ρ)^[B]) i=i) (k:ℕ) :
    cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i (B*k)=
      (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i B)^k := by
  let τ:=cofiniteTangentialCanonicalIndex ρ
  let W:=cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  have hLabel (j:ℕ):(τ^[B+j]) i=(τ^[j]) i:=by
    rw [Nat.add_comm B j,Function.iterate_add_apply,hReturn]
  have hAdd:∀j:ℕ,W (B+j)=W B*W j:=by
    intro j
    induction j with
    | zero => exact (mul_one (W B)).symm
    | succ j ih =>
      change W (B+j)*(S.generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf (τ^[B+j] i)))⁻¹=
        W B*(W j*(S.generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf (τ^[j] i)))⁻¹)
      rw [hLabel,ih]
      exact mul_assoc _ _ _
  change W (B*k)=W B^k
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ,Nat.add_comm (B*k) B,hAdd,ih,pow_succ']

/-- Every genuine stabilizer element at an original vertex occurs in its
complete angular word list. Evaluation injectivity is proved by the actual
compact polygon construction, rather than supplied as an input. -/
theorem cofiniteTangential_vertex_fixed_word {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
    (i:Fin n) (N:ℕ) (hN:0<N)
    (hClose:((ρ.trans (finRotate n))^[N]) i=i) (hAngle:θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
    (g:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated)
    (hfix:g.val (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i) :
    ∃j:Fin N,g=cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j.val ∧
      ((cofiniteTangentialCanonicalIndex ρ)^[j.val]) i=i := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf i
  have hA6:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q hf S
    (cofiniteTangential_opposite_side_neighborhoods θ d hθ hd hb hf ρ hρ hθρ)
    (cofiniteTangential_canonical_cycle_conditions θ d hθ hd hb hf ρ hρ hθρ hPeriod)
  have hEval:Function.Injective S.evaluation:=
    (hA6.covering_homeomorph_of_compact S
      (S.native_metric_assumptions (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q hf)
        (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q hf))
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf).le (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf)).2.injective
  have hproj:S.project (g,p)=S.project (1,p):=by
    apply hEval
    exact hfix
  have hmem:(g,p)∈S.project ⁻¹' {S.project (1,p)}:=hproj
  rw [cofiniteTangentialCanonicalWord_whole_fiber θ d hθ hd hb hf ρ hρ hθρ i N hN hClose hAngle] at hmem
  obtain ⟨j,hj⟩:=hmem
  refine ⟨j,(congrArg Prod.fst hj).symm,?_⟩
  apply _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf
  exact congrArg (fun a:S.Copy=>a.2.val) hj

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The true full stabilizer order at an actual finite constructed vertex
is the prescribed cone order. Minimality concerns only the proven original
finite label permutation; all ambient stabilizer elements are exhausted. -/
theorem cofiniteTangential_vertex_stabilizer_card {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
    (i:Fin n) (B m:ℕ) (hB:0<B) (hm:0<m)
    (hReturn:((cofiniteTangentialCanonicalIndex ρ)^[B]) i=i)
    (hMin:∀j:ℕ,((cofiniteTangentialCanonicalIndex ρ)^[j]) i=i → B∣j)
    (hAngle:θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod (B*m)) :
    Nat.card (MulAction.stabilizer
      (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i))=m := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i
  let K:=MulAction.stabilizer S.Generated p
  let R:=cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i B
  have hRfix:R∈K:=by
    change R.val p=p
    have hh:=cofiniteTangentialCanonicalWord_center θ d hθ hd hb hf ρ hρ hθρ i B
    rw [hReturn] at hh
    exact hh
  let r:K:=⟨R,hRfix⟩
  have hReturnMany:∀k:ℕ,((cofiniteTangentialCanonicalIndex ρ)^[B*k]) i=i:=by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Nat.mul_succ,Function.iterate_add_apply,hReturn,ih]
  have hClose:((ρ.trans (finRotate n))^[B*m]) i=i:=hReturnMany m
  have hAll:∀h:K,h∈Subgroup.zpowers r:=by
    intro h
    obtain ⟨j,hj,hji⟩:=cofiniteTangential_vertex_fixed_word θ d hθ hd hb hf ρ hρ hθρ hPeriod
      i (B*m) (Nat.mul_pos hB hm) hClose hAngle h.val h.property
    obtain ⟨k,hjk⟩:=hMin j.val hji
    have hWord:h.val=R^k:=by
      rw [hj,hjk,cofiniteTangentialCanonicalWord_period_blocks θ d hθ hd hb hf ρ hρ hθρ i B hReturn k]
    have hh:h=r^k:=Subtype.ext hWord
    rw [hh]
    exact Subgroup.mem_zpowers_iff.mpr ⟨(k:ℤ),by rw [zpow_natCast]⟩
  have hCard:Nat.card K=orderOf r:=(orderOf_eq_card_of_forall_mem_zpowers hAll).symm
  have hOrder:orderOf r=m:=by
    rw [←orderOf_injective K.subtype Subtype.val_injective]
    exact cofiniteTangentialCanonicalWord_order θ d hθ hd hb hf ρ hρ hθρ i B m hB hm hReturn hAngle
  exact hCard.trans hOrder

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

open Fin.NatCast in
/-- An actual labelled base corner returns precisely at multiples of the full base length. -/
theorem cofiniteConstructionBaseIndex_return_iff_dvd (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hB:0<4*g+ms.length) (a:Fin (4*g+ms.length)) (j:ℕ) :
    ((cofiniteConstructionVertexStep g ms last)^[j])
      (cofiniteConstructionBaseIndex g ms last a)=cofiniteConstructionBaseIndex g ms last a ↔
        (4*g+ms.length)∣j := by
  let cofiniteBaseCountNeZero : NeZero (4*g+ms.length):=⟨Nat.ne_of_gt hB⟩
  have hrot (k:ℕ) : ((finRotate (4*g+ms.length))^[k]) a=a+(k:Fin (4*g+ms.length)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply',ih,finRotate_apply]
      simp only [Nat.cast_add,Nat.cast_one,add_assoc]
  rw [cofiniteConstructionBaseIndex_iterate,hrot]
  constructor
  · intro he
    have h:=cofiniteConstructionBaseIndex_injective g ms last he
    have hz:(j:Fin (4*g+ms.length))=0:=
      add_left_cancel (h.trans (add_zero a).symm)
    exact Fin.natCast_eq_zero.mp hz
  · intro hj
    have hz:(j:Fin (4*g+ms.length))=0:=Fin.natCast_eq_zero.mpr hj
    rw [hz,add_zero]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The actual finite construction's original pairing, with every geometry
proof computed from the prescribed signature and positive deficit. -/
def cofiniteConstructionFinitePairing (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]) d=Real.pi) :
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf) :=
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)

/-- Each genuine finite vertex of the same actual prescribed polygon. -/
def cofiniteConstructionFiniteVertex (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]) d=Real.pi)
    (i:Fin (cofiniteConstructionAngles g ms last).length) :ℍ :=
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i

/-- The true full stabilizer of every original base vertex has precisely
the last prescribed cone order, internally exhausting all ambient elements. -/
theorem cofiniteConstruction_base_stabilizer_card (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]) d=Real.pi)
    (a:Fin (4*g+ms.length)) :
    Nat.card (MulAction.stabilizer
      (cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated
      (cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
        (cofiniteConstructionBaseIndex g ms last a)))=last := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let ρ:=cofiniteConstructionPairing g ms last
  have hB:0<4*g+ms.length:=lt_of_lt_of_le (by decide:0<2)
    (cofiniteConstruction_base_count g ms last hdef)
  apply cofiniteTangential_vertex_stabilizer_card θ d hθ hd hb hf ρ
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
    (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef)
    (cofiniteConstructionBaseIndex g ms last a) (4*g+ms.length) last hB (by omega)
  · exact cofiniteConstructionBaseIndex_full_turn g ms last a
  · intro j hj
    exact (cofiniteConstructionBaseIndex_return_iff_dvd g ms last hB a j).mp hj
  · dsimp only [θ]
    rw [cofiniteConstructionBaseIndex_angle]
    dsimp only [cofiniteConstructionBaseAngle,cofiniteConstructionConeAngle,_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod]
    push_cast
    rw [div_div]
    congr 1
    ring

/-- Every literal outer occurrence retains its own original full elliptic
order; equal numerical entries do not identify distinct cone labels. -/
theorem cofiniteConstruction_outer_stabilizer_card (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]) d=Real.pi)
    (a:{j:Fin ms.length //ms[j]≠2}) :
    Nat.card (MulAction.stabilizer
      (cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated
      (cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
        (cofiniteConstructionOuterIndex g ms last a)))=ms[a.val] := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let ρ:=cofiniteConstructionPairing g ms last
  have hm:0<ms[a.val]:=lt_of_lt_of_le (by decide:0<2) (hms _ (List.getElem_mem a.val.isLt))
  apply cofiniteTangential_vertex_stabilizer_card θ d hθ hd hb hf ρ
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
    (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef)
    (cofiniteConstructionOuterIndex g ms last a) 1 ms[a.val] (by decide) hm
  · exact cofiniteConstructionOuterIndex_fixed g ms last a
  · intro j _hj
    exact one_dvd j
  · dsimp only [θ]
    rw [cofiniteConstructionOuterIndex_angle,one_mul]
    rfl

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- Two actual original vertices are whole-group equivalent exactly when
the actual natural side-label permutation connects them. In particular equal
angle values alone never identify distinct prescribed cone occurrences. -/
theorem cofiniteTangential_vertex_orbit_iff {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) (i k:Fin n) :
    (∃g:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated,
      g.val (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i)=
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf k) ↔
      ∃j:ℕ,((cofiniteTangentialCanonicalIndex ρ)^[j]) i=k := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  constructor
  · rintro ⟨g,hg⟩
    have hA6:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q hf S
      (cofiniteTangential_opposite_side_neighborhoods θ d hθ hd hb hf ρ hρ hθρ)
      (cofiniteTangential_canonical_cycle_conditions θ d hθ hd hb hf ρ hρ hθρ hPeriod)
    have hEval:Function.Injective S.evaluation:=
      (hA6.covering_homeomorph_of_compact S
        (S.native_metric_assumptions (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q hf)
          (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q hf))
        (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf).le (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf)).2.injective
    obtain ⟨N,hN,hClose,hAngle⟩:=hPeriod i
    have hproj:S.project (g⁻¹,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf k)=
        S.project (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf i):=by
      apply hEval
      change g.val⁻¹ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf k)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i
      rw [←hg,IsometryEquiv.inv_apply_self]
    have hmem:(g⁻¹,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf k)∈
        S.project ⁻¹' {S.project (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf i)}:=hproj
    rw [cofiniteTangentialCanonicalWord_whole_fiber θ d hθ hd hb hf ρ hρ hθρ i N (by omega) hClose hAngle] at hmem
    obtain ⟨j,hj⟩:=hmem
    refine ⟨j.val,?_⟩
    apply _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf
    exact congrArg (fun a:S.Copy=>a.2.val) hj
  · rintro ⟨j,hj⟩
    refine ⟨(cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j)⁻¹,?_⟩
    have h:=cofiniteTangentialCanonicalWord_center θ d hθ hd hb hf ρ hρ hθρ i j
    rw [hj] at h
    apply (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val.injective
    change (cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val
      ((cofiniteTangentialCanonicalWord θ d hθ hd hb hf ρ hρ hθρ i j).val⁻¹
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i))=_
    rw [IsometryEquiv.apply_inv_self]
    exact h.symm

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The actual prescribed group's vertex orbits are its exact original
label cycles, with every geometric premise internally established. -/
theorem cofiniteConstruction_finite_vertex_orbit_iff (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>
      (cofiniteConstructionAngles g ms last)[i]) d=Real.pi)
    (i k:Fin (cofiniteConstructionAngles g ms last).length) :
    (∃f:(cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated,
      f.val (cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb i)=
        cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb k) ↔
      ∃j:ℕ,((cofiniteConstructionVertexStep g ms last)^[j]) i=k := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  exact cofiniteTangential_vertex_orbit_iff θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
    (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef) i k

/-- One actual original corner for the base cone and each separately labelled
outer cone of order different from two. The missing two marks are self-side centers. -/
def cofiniteConstructionConeIndex (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hdef:0<cofiniteConstructionDeficit g ms last) :
    Option {j:Fin ms.length //ms[j]≠2}→Fin (cofiniteConstructionAngles g ms last).length
  | none=>cofiniteConstructionBaseIndex g ms last
      ⟨0,lt_of_lt_of_le (by decide:0<2) (cofiniteConstruction_base_count g ms last hdef)⟩
  | some j=>cofiniteConstructionOuterIndex g ms last j

/-- These actual distinct corner representatives exhaust every original
finite vertex orbit, without excluding repeated numerical cone orders. -/
theorem cofiniteConstruction_vertex_representative_cover (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>
      (cofiniteConstructionAngles g ms last)[i]) d=Real.pi)
    (i:Fin (cofiniteConstructionAngles g ms last).length) :
    ∃c:Option {j:Fin ms.length //ms[j]≠2},
      ∃f:(cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated,
      f.val (cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
        (cofiniteConstructionConeIndex g ms last hdef c))=
      cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb i := by
  have hB:=cofiniteConstruction_base_count g ms last hdef
  obtain ⟨c,rfl⟩:=(cofiniteConstructionCornerLabelEquiv g ms last hB).surjective i
  cases c with
  | inl a =>
    rw [cofiniteConstructionCornerLabelEquiv_base]
    refine ⟨none,?_⟩
    apply (cofiniteConstruction_finite_vertex_orbit_iff g ms last hms hlast hdef d hd hb _ _).mpr
    obtain ⟨j,_hj,he⟩:=cofiniteConstructionBaseIndex_one_cycle g ms last (by omega) a
    exact ⟨j,he⟩
  | inr j =>
    rw [cofiniteConstructionCornerLabelEquiv_outer]
    exact ⟨some j,1,rfl⟩

/-- Whole-group equivalence of two actual original cone representatives
forces equality of their independent original labels. -/
theorem cofiniteConstruction_vertex_representatives_distinct (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>
      (cofiniteConstructionAngles g ms last)[i]) d=Real.pi)
    (c e:Option {j:Fin ms.length //ms[j]≠2})
    (he:∃f:(cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated,
      f.val (cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
        (cofiniteConstructionConeIndex g ms last hdef c))=
      cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
        (cofiniteConstructionConeIndex g ms last hdef e)) :c=e := by
  obtain ⟨j,hj⟩:=(cofiniteConstruction_finite_vertex_orbit_iff g ms last hms hlast hdef d hd hb _ _).mp he
  have hIter (a:{j:Fin ms.length //ms[j]≠2}) (t:ℕ):
      ((cofiniteConstructionVertexStep g ms last)^[t]) (cofiniteConstructionOuterIndex g ms last a)=
        cofiniteConstructionOuterIndex g ms last a:=by
    have hfix:=cofiniteConstructionOuterIndex_fixed g ms last a
    induction t with
    | zero=>rfl
    | succ j ih=>rw [Function.iterate_succ_apply,hfix,ih]
  cases c with
  | none=>
    cases e with
    | none=>rfl
    | some b=>
      dsimp only [cofiniteConstructionConeIndex] at hj
      rw [cofiniteConstructionBaseIndex_iterate] at hj
      exact (cofiniteConstructionBaseIndex_ne_outer g ms last
        (cofiniteConstruction_base_count g ms last hdef) _ b hj).elim
  | some a=>
    cases e with
    | none=>
      dsimp only [cofiniteConstructionConeIndex] at hj
      rw [hIter] at hj
      exact (cofiniteConstructionBaseIndex_ne_outer g ms last
        (cofiniteConstruction_base_count g ms last hdef) _ a hj.symm).elim
    | some b=>
      dsimp only [cofiniteConstructionConeIndex] at hj
      rw [hIter] at hj
      exact congrArg Option.some (cofiniteConstructionOuterIndex_injective g ms last hj)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

section ProjectiveModel
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))

/-- Every generator of the actual common-incircle group is positively conformal. -/
theorem cofiniteTangentialGenerated_conformal :
    (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨s,rfl⟩
  obtain ⟨i,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf).surjective s
  rw [cofiniteTangentialSidePairing_element_index]
  exact cofiniteTangentPairingElement_conformal θ d hθ hd hb i (ρ i)

/-- The genuine projective boundary representation of the actual native group. -/
def cofiniteTangentialToMobius :
    (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated→*
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  nativeConformalSubgroupMobiusHom _
    (cofiniteTangentialGenerated_conformal θ d hθ hd hb hf ρ hρ hθρ)

/-- The entire faithful image of the original generated group. -/
def cofiniteTangentialMobiusGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  (cofiniteTangentialToMobius θ d hθ hd hb hf ρ hρ hθρ).range

/-- The native and projective groups differ only in their subtype labels. -/
def cofiniteTangentialGroupEquiv :
    (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated≃*
      cofiniteTangentialMobiusGroup θ d hθ hd hb hf ρ hρ hθρ :=
  MulEquiv.ofBijective
    (cofiniteTangentialToMobius θ d hθ hd hb hf ρ hρ hθρ).rangeRestrict
    ⟨fun _a _b h=>(nativeConformalSubgroupMobiusHom_isometry _
      (cofiniteTangentialGenerated_conformal θ d hθ hd hb hf ρ hρ hθρ)).injective
        (congrArg Subtype.val h),
      (cofiniteTangentialToMobius θ d hθ hd hb hf ρ hρ hθρ).rangeRestrict_surjective⟩

variable (hPeriod:∀i:Fin n,∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
include hPeriod

/-- The actual polygon construction supplies the genuine projective Fuchsian data. -/
theorem cofiniteTangentialHalfPlaneData :
    HalfPlaneFuchsianGroup (cofiniteTangentialMobiusGroup θ d hθ hd hb hf ρ hρ hθρ) := by
  let : DiscreteTopology
      (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated:=
    (cofiniteTangential_finite_poincare θ d hθ hd hb hf ρ hρ hθρ hPeriod).1
  exact nativeConformalSubgroup_halfPlaneData _
    (cofiniteTangentialGenerated_conformal θ d hθ hd hb hf ρ hρ hθρ)

/-- The equivalence intertwines the original action at every actual half-plane point. -/
theorem cofiniteTangentialGroupEquiv_action
    (g:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated) (z:ℍ) :
    letI:=(cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).nativeAction
    cofiniteTangentialGroupEquiv θ d hθ hd hb hf ρ hρ hθρ g • z=g.val z := by
  let originalAction:=
    (cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [←(cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).nativeAction_boundary]
  exact nativeConformalSubgroupMobiusHom_action _
    (cofiniteTangentialGenerated_conformal θ d hθ hd hb hf ρ hρ hθρ) g z

/-- The faithful projective group has the literal original polygon as fundamental domain. -/
theorem cofiniteTangential_projective_native_fundamental :
    letI:=(cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (cofiniteTangentialMobiusGroup θ d hθ hd hb hf ρ hρ hθρ)
      ℍ MeasureTheory.volume
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior) := by
  let originalAction:=
    (cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).nativeAction
  let e:=cofiniteTangentialGroupEquiv θ d hθ hd hb hf ρ hρ hθρ
  have he (g:cofiniteTangentialMobiusGroup θ d hθ hd hb hf ρ hρ hθρ) (z:ℍ) :
      (Homeomorph.refl ℍ) (g • z)=e.symm g • (Homeomorph.refl ℍ) z := by
    change g • z=(e.symm g).val z
    simpa only [e,MulEquiv.apply_symm_apply] using
      cofiniteTangentialGroupEquiv_action θ d hθ hd hb hf ρ hρ hθρ hPeriod (e.symm g) z
  have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e.symm (Homeomorph.refl ℍ) he
    (cofiniteTangential_finite_poincare θ d hθ hd hb hf ρ hρ hθρ hPeriod).2
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain _ ℍ
    (MeasureTheory.Measure.map id MeasureTheory.volume) (id ⁻¹' _) at h
  simpa only [MeasureTheory.Measure.map_id,preimage_id] using h

/-- The original polygon is a fundamental domain in the actual projective Cayley disc. -/
theorem cofiniteTangential_projective_disc_fundamental :
    let P:=cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
    IsFuchsianFundamentalDomain P.cayleyData
      (P.cayleyCoordinate ''
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior)) := by
  exact (cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).cayley_fundamental
    (cofiniteTangential_projective_native_fundamental θ d hθ hd hb hf ρ hρ hθρ hPeriod)

/-- The finite coordinate of this actual domain is exactly the original polygon interior. -/
theorem cofiniteTangential_projective_disc_finite_region :
    let P:=cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
    P.cayleyData.finiteCoordinate '' (P.cayleyCoordinate ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior))=
        (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior := by
  dsimp only
  rw [image_image]
  simp_rw [HalfPlaneFuchsianGroup.cayleyCoordinate_finite]
  exact image_preimage_eq _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.surjective

end ProjectiveModel
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open MeasureTheory
local instance tangentialCompactSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance tangentialCompactSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

section CompactPolygon
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)

/-- Only finitely many translates of the actual closed polygon meet a compact set. -/
theorem cofiniteTangential_projective_compact_tiles :
    letI:=(cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).nativeAction
    ∀K:Set ℍ,IsCompact K→
      {g:cofiniteTangentialMobiusGroup θ d hθ hd hb hf ρ hρ hθρ |
        (g • closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹'
          (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior) ∩ K).Nonempty}.Finite := by
  let originalAction:=
    (cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).nativeAction
  let nativeDiscrete : DiscreteTopology
      (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated:=
    (cofiniteTangential_finite_poincare θ d hθ hd hb hf ρ hρ hθρ hPeriod).1
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let e:=cofiniteTangentialGroupEquiv θ d hθ hd hb hf ρ hρ hθρ
  intro K hK
  have hcomp:IsCompact (closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior)) := by
    change IsCompact (closure (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior)
    rw [←_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf
  have hfin:=(native_compact_translate_hits_finite
    (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated hcomp hK).image e
  apply hfin.subset
  rintro g ⟨x,⟨y,hy,hgy⟩,hxK⟩
  refine ⟨e.symm g,⟨x,⟨y,hy,?_⟩,hxK⟩,e.apply_symm_apply g⟩
  have he:=cofiniteTangentialGroupEquiv_action θ d hθ hd hb hf ρ hρ hθρ hPeriod (e.symm g) y
  change e (e.symm g) • y=(e.symm g).val y at he
  rw [e.apply_symm_apply] at he
  exact he.symm.trans hgy

/-- The original common-incircle domain is a genuine convex Fuchsian polygon. -/
theorem cofiniteTangential_projective_disc_convex :
    let P:=cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
    IsConvexFuchsianPolygon P.cayleyData
      (P.cayleyCoordinate ''
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior)) := by
  apply (cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).cayley_polygon
    (cofiniteTangential_projective_native_fundamental θ d hθ hd hb hf ρ hρ hθρ hPeriod) ?_
    (cofiniteTangential_projective_compact_tiles θ d hθ hd hb hf ρ hρ hθρ hPeriod)
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex _).mpr
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph ⁻¹'
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior)
  rw [image_preimage_eq _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.surjective]
  exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb

/-- This actual projective fundamental polygon has compact closure. -/
theorem cofiniteTangential_projective_disc_closure_compact :
    let P:=cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
    IsCompact (closure (P.cayleyCoordinate ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior))) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let e:=(cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).cayleyCoordinate
  change IsCompact (closure (e '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior)))
  rw [←e.image_closure]
  change IsCompact (e '' closure (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior)
  rw [←_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf]
  exact (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf).image e.continuous

/-- Physical density area equals the area of the unchanged original polygon. -/
theorem cofiniteTangential_projective_disc_area :
    let P:=cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
    P.cayleyData.area (P.cayleyCoordinate ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior))=
        (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).area := by
  dsimp only
  have hopen:=(cofiniteTangential_projective_disc_fundamental
    θ d hθ hd hb hf ρ hρ hθρ hPeriod).isOpen
  rw [(cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod).cayleyData.area_apply
    _ hopen.measurableSet,
    cofiniteTangential_projective_disc_finite_region θ d hθ hd hb hf ρ hρ hθρ hPeriod]
  rfl

/-- The actual Fuchsian polygon has its prescribed original angle-defect area. -/
theorem cofiniteTangential_projective_disc_area_exact :
    let P:=cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
    P.cayleyData.area (P.cayleyCoordinate ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior))=
        ENNReal.ofReal (((n:ℝ)-2)*Real.pi-∑i:Fin n,θ i) := by
  dsimp only
  rw [cofiniteTangential_projective_disc_area θ d hθ hd hb hf ρ hρ hθρ hPeriod,
    _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.area_eq_original_angle_defect]
  simp_rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]

/-- The genuine physical area is finite. -/
theorem cofiniteTangential_projective_disc_area_lt_top :
    let P:=cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
    P.cayleyData.area (P.cayleyCoordinate ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior))<⊤ := by
  dsimp only
  rw [cofiniteTangential_projective_disc_area θ d hθ hd hb hf ρ hρ hθρ hPeriod]
  exact (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).area_lt_top

end CompactPolygon
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The physical contact point lies on the original whole side. -/
theorem cofiniteTangential_foot_mem_side {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))∈
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))))∈
      _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_foot_mem_edge θ d hθ hd hb i

/-- The actual self-side radial mirror fixes its own original contact point. -/
theorem cofiniteTangentMirror_self_foot {n:ℕ} (θ:Fin n→ℝ) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) :
    cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i i)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)))=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
  simp only [cofiniteClosedOrthogonal_klein,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot_coordinate,map_smul,
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_unit_next θ d hb i,cofiniteTangentMirror_unit]
  rw [show _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (i.val+1)+_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (i.val+1)-
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (i.val+1)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (i.val+1) by ring]

/-- The actual native self-pairing fixes the true incircle contact point. -/
theorem cofiniteTangentPairingElement_self_foot {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n) :
    cofiniteTangentPairingElement θ d hθ hd hb i i
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)))=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i i)
  have hM:M w=w:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i i)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)))))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))))
    simp only [cofiniteTangentMirror_native_commutes,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    exact cofiniteTangentMirror_self_foot θ d hd hb i
  have hR:(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).reflection w=w:=
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).reflection_fixed_iff w).mpr
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i (cofiniteTangential_foot_mem_side θ d hθ hd hb i))
  change M ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).reflection w)=w
  rw [hR,hM]

/-- Each genuine positive side element has at most one physical interior fixed point. -/
theorem cofiniteTangentPairingElement_fixed_subsingleton {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n) :
    Set.Subsingleton {z:ℍ|cofiniteTangentPairingElement θ d hθ hd hb i j z=z} := by
  obtain ⟨A,hA⟩:=cofiniteTangentPairingElement_conformal θ d hθ hd hb i j
  apply nativePositiveGL_fixedSet_subsingleton _
    (cofiniteTangentPairingElement_ne_one θ d hθ hd hb i j) A.toGL
  · change 0<(A:Matrix (Fin 2) (Fin 2) ℝ).det
    rw [A.det_coe]
    exact zero_lt_one
  · intro z
    rw [←hA]
    rfl

section FiniteSelfCenters
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
include hθρ

/-- A genuine self-side contact point is none of the actual finite polygon vertices. -/
theorem cofiniteTangential_self_foot_nonvertex (i:Fin n) (hi:ρ i=i) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))∉
      range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))
  let A:=cofiniteTangentPairingElement θ d hθ hd hb i i
  have hfix:A w=w:=cofiniteTangentPairingElement_self_foot θ d hθ hd hb i
  have hleft:w≠_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i:=by
    intro he
    have hz:_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)):=
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate Q hf i).symm
    have hp:=cofiniteTangential_outgoing_orientation θ d hθ hd hb i _ hz
    have hcoord:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)=
        _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i):=by
      rw [←he]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane _
    rw [hcoord] at hp
    exact (lt_irrefl (0:ℝ)) (by
      simpa only [OriginalOrientation.signedArea,sub_self,map_zero,zero_mul,Complex.zero_im] using hp)
  have hvertex:A (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (finRotate n i):=by
    have h:=cofiniteTangentialPairing_finite_vertex θ d hθ hd hb hf ρ hθρ i
    simpa only [hi,cofiniteTangentialCanonicalIndex,Equiv.trans_apply] using h
  have hright:w≠_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (finRotate n i):=by
    intro he
    apply hleft
    apply A.injective
    exact hfix.trans (he.trans hvertex.symm)
  rintro ⟨j,hj⟩
  have hside:_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf j∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i:=
    hj ▸ cofiniteTangential_foot_mem_side θ d hθ hd hb i
  rcases (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_side_iff Q hf j i).mp hside with he|he
  · have hj':j=finRotate n i:=by rw [he];exact ((finRotate n).apply_symm_apply j).symm
    exact hright (hj.symm.trans (congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf) hj'))
  · exact hleft (hj.symm.trans (congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf) he.symm))

variable (hPeriod:∀i:Fin n,∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
include hPeriod

/-- Any nonidentity whole-group fixer at a side nonvertex is exactly its true self-pairing. -/
theorem cofiniteTangential_side_nonvertex_fixing (i:Fin n) (x:ℍ)
    (hx:x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i)
    (hv:x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf))
    (g:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated)
    (hfix:g.val x=x) :
    g=1 ∨ ρ i=i ∧ g=(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).generator
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let s:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i
  let p:P.Point:=⟨x,P.side_subset_carrier s hx⟩
  let generatedIsometric:IsIsometricSMul S.Generated ℍ:=⟨fun h=>h.val.isometry⟩
  have hA:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q hf S
    (cofiniteTangential_opposite_side_neighborhoods θ d hθ hd hb hf ρ hρ hθρ)
    (cofiniteTangential_canonical_cycle_conditions θ d hθ hd hb hf ρ hρ hθρ hPeriod)
  have hEval:Function.Injective S.evaluation:=
    (hA.covering_homeomorph_of_compact S
      (S.native_metric_assumptions (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q hf)
        (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q hf))
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf).le (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf)).2.injective
  have hproj:S.project (g,p)=S.project (1,p):=by apply hEval;exact hfix
  have hmate:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_pairing_nonvertex Q hf S i hx hv
  have hu:∀t:P.Side,x∈t.val→t=s:=by
    intro t ht
    obtain ⟨j,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective t
    by_cases he:i=j
    · exact congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) he.symm
    · exact (hv (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q hf he hx ht)).elim
  have hw:∀t:P.Side,(S.sideMateCopy (1,p) s hx).2.val∈t.val→t=S.paired s:=by
    intro t ht
    let y:=S.generator s • x
    have hy:y∈(S.paired s).val:=by rw [←S.generator_side_image];exact ⟨x,hx,rfl⟩
    obtain ⟨j,hj⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective (S.paired s)
    obtain ⟨l,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective t
    by_cases he:j=l
    · exact (congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) he.symm).trans hj
    · have hyj:y∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q j:=by change y∈((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) j).val;rw [hj];exact hy
      exact (hmate (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q hf he hyj ht)).elim
  have hm:(g,p)∈S.project ⁻¹' {S.project (1,p)}:=hproj
  rw [S.project_fiber_eq_side_pair (1,p) s hx hu hw] at hm
  rcases hm with he|he
  · exact Or.inl (congrArg Prod.fst he)
  · have hcoord:x=S.generator s • x:=congrArg (fun a:S.Copy=>a.2.val) he
    have hother:x∈(S.paired s).val:=by rw [hcoord,←S.generator_side_image];exact ⟨x,hx,rfl⟩
    have hlabel:ρ i=i:=by
      by_contra hne
      rw [cofiniteTangentialSidePairing_paired_index θ d hθ hd hb hf ρ hρ hθρ i] at hother
      exact hv (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q hf (fun h=>hne h.symm) hx hother)
    have hp:S.paired s=s:=by
      rw [cofiniteTangentialSidePairing_paired_index θ d hθ hd hb hf ρ hρ hθρ i,hlabel]
    have hinv:(S.generator s)⁻¹=S.generator s:=
      (S.generator_paired s).symm.trans (congrArg S.generator hp)
    exact Or.inr ⟨hlabel,by simpa only [_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.sideMateCopy,one_mul,hinv] using congrArg Prod.fst he⟩

/-- Every actual nonvertex elliptic center on an original side is its genuine self-side contact point. -/
theorem cofiniteTangential_side_nonvertex_fixed_center (i:Fin n) (x:ℍ)
    (hx:x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i)
    (hv:x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf))
    (g:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated)
    (hg:g≠1) (hfix:g.val x=x) :
    ρ i=i ∧ x=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)) ∧
      g=(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).generator
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i) := by
  rcases cofiniteTangential_side_nonvertex_fixing θ d hθ hd hb hf ρ hρ hθρ hPeriod i x hx hv g hfix
      with he|⟨hself,he⟩
  · exact False.elim (hg he)
  · refine ⟨hself,?_,he⟩
    have hAx:cofiniteTangentPairingElement θ d hθ hd hb i i x=x:=by
      rw [he] at hfix
      change (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).element
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i) x=x at hfix
      rw [cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ i,hself] at hfix
      exact hfix
    exact cofiniteTangentPairingElement_fixed_subsingleton θ d hθ hd hb i i hAx
      (cofiniteTangentPairingElement_self_foot θ d hθ hd hb i)

/-- The entire native generated group has exactly order two at each actual self-side contact point. -/
theorem cofiniteTangential_self_foot_stabilizer_card (i:Fin n) (hi:ρ i=i) :
    Nat.card (MulAction.stabilizer
      (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))))=2 := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let s:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i
  let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))
  have hfix:S.generator s • w=w:=by
    change S.element s w=w
    rw [cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ i,hi]
    exact cofiniteTangentPairingElement_self_foot θ d hθ hd hb i
  let r:MulAction.stabilizer S.Generated w:=⟨S.generator s,hfix⟩
  have hr:r≠1:=by
    intro he
    have hv:S.element s=1:=congrArg (fun a:MulAction.stabilizer S.Generated w=>a.val.val) he
    rw [cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ i] at hv
    exact cofiniteTangentPairingElement_ne_one θ d hθ hd hb i (ρ i) hv
  apply (Nat.card_eq_two_iff' (1:MulAction.stabilizer S.Generated w)).mpr
  refine ⟨r,hr,?_⟩
  intro k hk
  have h:=cofiniteTangential_side_nonvertex_fixing θ d hθ hd hb hf ρ hρ hθρ hPeriod i w
    (cofiniteTangential_foot_mem_side θ d hθ hd hb i)
    (cofiniteTangential_self_foot_nonvertex θ d hθ hd hb hf ρ hθρ i hi) k.val k.property
  rcases h with he|⟨_hself,he⟩
  · exact False.elim (hk (Subtype.ext he))
  · exact Subtype.ext he

/-- The original native and actual Cayley-disc whole stabilizers are isomorphic under the physical coordinate. -/
def cofiniteTangential_projective_disc_stabilizerEquiv (x:ℍ) :
    let P:=cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
    MulAction.stabilizer
      (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated x ≃*
        MulAction.stabilizer
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteTangentialMobiusGroup θ d hθ hd hb hf ρ hρ hθρ))
          (P.cayleyCoordinate x) := by
  dsimp only
  let P:=cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let E:=(cofiniteTangentialGroupEquiv θ d hθ hd hb hf ρ hρ hθρ).trans
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteTangentialMobiusGroup θ d hθ hd hb hf ρ hρ hθρ))
  have hAct (g:S.Generated) (z:ℍ) : P.cayleyCoordinate (g.val z)=E g • P.cayleyCoordinate z := by
    have h:=P.cayleyCoordinate_equivariant
      (cofiniteTangentialGroupEquiv θ d hθ hd hb hf ρ hρ hθρ g) z
    rw [cofiniteTangentialGroupEquiv_action θ d hθ hd hb hf ρ hρ hθρ hPeriod] at h
    exact h
  refine {
    toFun:=fun g=>⟨E g.val,(hAct g.val x).symm.trans (congrArg P.cayleyCoordinate g.property)⟩
    invFun:=fun g=>⟨E.symm g.val,?_⟩
    left_inv:=fun g=>Subtype.ext (E.symm_apply_apply g.val)
    right_inv:=fun g=>Subtype.ext (E.apply_symm_apply g.val)
    map_mul':=fun g h=>Subtype.ext (E.map_mul g.val h.val)
  }
  apply P.cayleyCoordinate.injective
  change P.cayleyCoordinate ((E.symm g.val).val x)=P.cayleyCoordinate x
  rw [hAct,E.apply_symm_apply]
  exact g.property

/-- Actual native stabilizer cardinalities are exactly the original Fuchsian point orders. -/
theorem cofiniteTangential_projective_disc_pointOrder (x:ℍ) :
    let P:=cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
    fuchsianPointOrder P.cayleyData (P.cayleyCoordinate x)=
      Nat.card (MulAction.stabilizer
        (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated x) := by
  exact (Nat.card_congr
    (cofiniteTangential_projective_disc_stabilizerEquiv θ d hθ hd hb hf ρ hρ hθρ hPeriod x).toEquiv).symm

end FiniteSelfCenters
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The literal marked-block pairing fixes exactly the unique side of each order-two occurrence. -/
theorem cofiniteConstructionMarkPairNat_fixed_iff (α:ℝ) (ms:List ℕ) (i:ℕ)
    (hi:i<(cofiniteConstructionMarkAngles α ms).length) :
    cofiniteConstructionMarkPairNat ms i=i ↔
      ∃j:Fin ms.length,ms[j]=2 ∧ cofiniteConstructionMarkBaseNat ms j.val=i := by
  induction ms generalizing i with
  | nil => simp [cofiniteConstructionMarkAngles] at hi
  | cons m ms ih =>
    let w:ℕ:=if m=2 then 1 else 2
    have hw:0<w:=by dsimp only [w];split_ifs <;> omega
    by_cases hit:i<w
    · by_cases hm:m=2
      · have hi0:i=0:=by
          have h:i<1:=by simpa only [w,hm,ite_true] using hit
          omega
        subst i
        constructor
        · intro _
          exact ⟨⟨0,by simp⟩,hm,rfl⟩
        · intro _
          simp [cofiniteConstructionMarkPairNat,hm]
      · have hi2:i<2:=by simpa only [w,hm,ite_false] using hit
        constructor
        · intro he
          rw [cofiniteConstructionMarkPairNat,ite_eq_right hm,ite_eq_left hi2] at he
          omega
        · rintro ⟨j,hj,hbase⟩
          cases j using Fin.cases with
          | zero => exact False.elim (hm hj)
          | succ j =>
            change w+cofiniteConstructionMarkBaseNat ms j.val=i at hbase
            omega
    · obtain ⟨k,rfl⟩:∃k,i=w+k:=⟨i-w,by omega⟩
      have hlen:(cofiniteConstructionMarkAngles α (m::ms)).length=
          w+(cofiniteConstructionMarkAngles α ms).length:=by
        by_cases hm:m=2 <;>
          simp only [cofiniteConstructionMarkAngles,w,hm,ite_true,ite_false,List.length_cons] <;>
          omega
      have hk:k<(cofiniteConstructionMarkAngles α ms).length:=by rw [hlen] at hi;omega
      change cofiniteConstructionMarkPairNat (m::ms) ((if m=2 then 1 else 2)+k)=_ ↔ _
      rw [cofiniteConstructionMarkPairNat_shift]
      constructor
      · intro he
        obtain ⟨j,hj,hbase⟩:=(ih k hk).mp (by change w+_ =w+k at he;omega)
        refine ⟨j.succ,by simpa using hj,?_⟩
        change w+cofiniteConstructionMarkBaseNat ms j.val=w+k
        rw [hbase]
      · rintro ⟨j,hj,hbase⟩
        cases j using Fin.cases with
        | zero =>
          change 0=w+k at hbase
          omega
        | succ j =>
          change w+cofiniteConstructionMarkBaseNat ms j.val=w+k at hbase
          have he:=(ih k hk).mpr ⟨j,by simpa using hj,Nat.add_left_cancel hbase⟩
          change w+cofiniteConstructionMarkPairNat ms k=w+k
          rw [he]

/-- No handle side is fixed; the remaining fixed labels are the literal order-two marks. -/
theorem cofiniteConstructionPairNat_fixed_iff (α:ℝ) (g:ℕ) (ms:List ℕ) (i:ℕ)
    (hi:i<(cofiniteConstructionSideAngles α g ms).length) :
    cofiniteConstructionPairNat g ms i=i ↔
      ∃j:Fin ms.length,ms[j]=2 ∧ 4*g+cofiniteConstructionMarkBaseNat ms j.val=i := by
  induction g generalizing i with
  | zero => simpa only [cofiniteConstructionPairNat,Nat.mul_zero,Nat.zero_add] using
      cofiniteConstructionMarkPairNat_fixed_iff α ms i hi
  | succ g ih =>
    by_cases hi4:i<4
    · constructor
      · intro he
        rw [cofiniteConstructionPairNat,ite_eq_left hi4] at he
        split_ifs at he <;> omega
      · rintro ⟨j,_hj,he⟩
        omega
    · obtain ⟨k,rfl⟩:∃k,i=4+k:=⟨i-4,by omega⟩
      have hk:k<(cofiniteConstructionSideAngles α g ms).length:=by
        rw [cofiniteConstructionSideAngles_handle] at hi
        simp only [List.length_cons] at hi
        omega
      rw [cofiniteConstructionPairNat_shift]
      constructor
      · intro he
        obtain ⟨j,hj,hbase⟩:=(ih k hk).mp (Nat.add_left_cancel he)
        exact ⟨j,hj,by omega⟩
      · rintro ⟨j,hj,hbase⟩
        have he:=(ih k hk).mpr ⟨j,hj,by omega⟩
        rw [he]

/-- The original side label of an order-two occurrence; repeated marks remain distinct. -/
def cofiniteConstructionSelfSideIndex (g:ℕ) (ms:List ℕ) (last:ℕ)
    (j:{j:Fin ms.length // ms[j]=2}) : Fin (cofiniteConstructionAngles g ms last).length :=
  ⟨4*g+cofiniteConstructionMarkBaseNat ms j.val.val,by
    have hb:=cofiniteConstructionMarkBaseNat_bound
      (cofiniteConstructionBaseAngle g ms last) ms j.val.val j.val.isLt
    have hlen:=congrArg List.length (cofiniteConstructionAngles_eq_sideAngles g ms last)
    simp only [cofiniteConstructionSideAngles,List.length_append,List.length_replicate] at hlen
    omega⟩

theorem cofiniteConstructionSelfSideIndex_val (g:ℕ) (ms:List ℕ) (last:ℕ)
    (j:{j:Fin ms.length // ms[j]=2}) :
    (cofiniteConstructionSelfSideIndex g ms last j).val=
      4*g+cofiniteConstructionMarkBaseNat ms j.val.val := rfl

theorem cofiniteConstructionSelfSideIndex_injective (g:ℕ) (ms:List ℕ) (last:ℕ) :
    Function.Injective (cofiniteConstructionSelfSideIndex g ms last) := by
  intro i j he
  apply Subtype.ext
  apply Fin.ext
  apply cofiniteConstructionMarkBaseNat_injective ms
  exact Nat.add_left_cancel (congrArg Fin.val he)

/-- Each displayed original side really is fixed by the unchanged literal pairing. -/
theorem cofiniteConstructionSelfSideIndex_fixed (g:ℕ) (ms:List ℕ) (last:ℕ)
    (j:{j:Fin ms.length // ms[j]=2}) :
    cofiniteConstructionPairing g ms last (cofiniteConstructionSelfSideIndex g ms last j)=
      cofiniteConstructionSelfSideIndex g ms last j := by
  apply Fin.ext
  rw [cofiniteConstructionPairing_val,cofiniteConstructionSelfSideIndex_val,
    cofiniteConstructionPairNat_handle_prefix]
  have hb:=cofiniteConstructionMarkBaseNat_bound
    (cofiniteConstructionBaseAngle g ms last) ms j.val.val j.val.isLt
  have he:=(cofiniteConstructionMarkPairNat_fixed_iff
    (cofiniteConstructionBaseAngle g ms last) ms _ hb).mpr ⟨j.val,j.property,rfl⟩
  rw [he]

/-- Exhaustion is by literal occurrence labels, with no numerical-angle coincidence restriction. -/
theorem cofiniteConstructionPairing_fixed_iff (g:ℕ) (ms:List ℕ) (last:ℕ)
    (i:Fin (cofiniteConstructionAngles g ms last).length) :
    cofiniteConstructionPairing g ms last i=i ↔
      ∃j:{j:Fin ms.length // ms[j]=2},cofiniteConstructionSelfSideIndex g ms last j=i := by
  constructor
  · intro he
    have hi:i.val<(cofiniteConstructionSideAngles
        (cofiniteConstructionBaseAngle g ms last) g ms).length:=
      i.isLt.trans_eq (congrArg List.length (cofiniteConstructionAngles_eq_sideAngles g ms last))
    have hn:cofiniteConstructionPairNat g ms i.val=i.val:=congrArg Fin.val he
    obtain ⟨j,hj,hbase⟩:=(cofiniteConstructionPairNat_fixed_iff
      (cofiniteConstructionBaseAngle g ms last) g ms i.val hi).mp hn
    exact ⟨⟨j,hj⟩,Fin.ext hbase⟩
  · rintro ⟨j,rfl⟩
    exact cofiniteConstructionSelfSideIndex_fixed g ms last j

/-- Exact fixed-side labels correspond to every order-two list occurrence, including repetitions. -/
def cofiniteConstructionSelfSideLabelEquiv (g:ℕ) (ms:List ℕ) (last:ℕ) :
    {i:Fin (cofiniteConstructionAngles g ms last).length // cofiniteConstructionPairing g ms last i=i} ≃
      {j:Fin ms.length // ms[j]=2} :=
  (Equiv.ofBijective (fun j:{j:Fin ms.length // ms[j]=2}=>
    (⟨cofiniteConstructionSelfSideIndex g ms last j,
      cofiniteConstructionSelfSideIndex_fixed g ms last j⟩:
        {i:Fin (cofiniteConstructionAngles g ms last).length // cofiniteConstructionPairing g ms last i=i}))
    ⟨fun _ _ h=>cofiniteConstructionSelfSideIndex_injective g ms last (congrArg Subtype.val h),
      fun i=>by
        obtain ⟨j,hj⟩:=(cofiniteConstructionPairing_fixed_iff g ms last i.val).mp i.property
        exact ⟨j,Subtype.ext hj⟩⟩).symm

/-- The correspondence's inverse retains the actual original side index. -/
theorem cofiniteConstructionSelfSideLabelEquiv_symm_index (g:ℕ) (ms:List ℕ) (last:ℕ)
    (j:{j:Fin ms.length // ms[j]=2}) :
    ((cofiniteConstructionSelfSideLabelEquiv g ms last).symm j).val=
      cofiniteConstructionSelfSideIndex g ms last j := rfl

/-- The number of original self-paired sides counts order-two occurrences with multiplicity. -/
theorem cofiniteConstructionSelfSideLabelEquiv_card (g:ℕ) (ms:List ℕ) (last:ℕ) :
    Nat.card {i:Fin (cofiniteConstructionAngles g ms last).length //
        cofiniteConstructionPairing g ms last i=i}=
      Nat.card {j:Fin ms.length // ms[j]=2} :=
  Nat.card_congr (cofiniteConstructionSelfSideLabelEquiv g ms last)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

section ActualConeOrbits
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)

/-- A self-side center has exactly its two original copies in the actual
point-gluing fiber, including their unchanged physical source point. -/
theorem cofiniteTangential_self_foot_fiber_points (i:Fin n) (hi:ρ i=i)
    (a:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Copy)
    (ha:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).project a=
      (cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).project
        (1,⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)),
          (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf).side_subset_carrier
            (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i)
            (cofiniteTangential_foot_mem_side θ d hθ hd hb i)⟩)) :
    a.2.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let s:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i
  let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))
  have hw:w∈s.val:=cofiniteTangential_foot_mem_side θ d hθ hd hb i
  let p:P.Point:=⟨w,P.side_subset_carrier s hw⟩
  have hnv:=cofiniteTangential_self_foot_nonvertex θ d hθ hd hb hf ρ hθρ i hi
  have hfix:S.generator s • w=w:=by
    change S.element s w=w
    rw [cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ i,hi]
    exact cofiniteTangentPairingElement_self_foot θ d hθ hd hb i
  have hu:∀t:P.Side,w∈t.val→t=s:=by
    intro t ht
    obtain ⟨j,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective t
    by_cases he:i=j
    · exact congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) he.symm
    · exact False.elim (hnv (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q hf he hw ht))
  have hp:S.paired s=s:=by
    rw [cofiniteTangentialSidePairing_paired_index θ d hθ hd hb hf ρ hρ hθρ i,hi]
  have hv:∀t:P.Side,(S.sideMateCopy (1,p) s hw).2.val∈t.val→t=S.paired s:=by
    intro t ht
    change S.generator s • w∈t.val at ht
    rw [hfix] at ht
    exact (hu t ht).trans hp.symm
  have hm:a∈S.project ⁻¹' {S.project (1,p)}:=ha
  rw [S.project_fiber_eq_side_pair (1,p) s hw hu hv] at hm
  rcases hm with he|he
  · exact congrArg (fun b:S.Copy=>b.2.val) he
  · exact (congrArg (fun b:S.Copy=>b.2.val) he).trans hfix

include hPeriod

/-- Distinct original self-side labels give distinct whole-group center orbits. -/
theorem cofiniteTangential_self_foot_orbits_distinct (i j:Fin n)
    (hi:ρ i=i) (hj:ρ j=j)
    (g:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated)
    (he:g.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n j))) :i=j := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let p (k:Fin n):P.Point:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n k)),
    P.side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf k)
      (cofiniteTangential_foot_mem_side θ d hθ hd hb k)⟩
  have hA:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q hf S
    (cofiniteTangential_opposite_side_neighborhoods θ d hθ hd hb hf ρ hρ hθρ)
    (cofiniteTangential_canonical_cycle_conditions θ d hθ hd hb hf ρ hρ hθρ hPeriod)
  have hEval:Function.Injective S.evaluation:=
    (hA.covering_homeomorph_of_compact S
      (S.native_metric_assumptions (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q hf)
        (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q hf))
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf).le (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf)).2.injective
  have hp:S.project (g,p i)=S.project (1,p j):=by apply hEval;exact he
  have hphys:=cofiniteTangential_self_foot_fiber_points θ d hθ hd hb hf ρ hρ hθρ j hj (g,p i) hp
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n j)) at hphys
  by_contra hne
  have hside:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q j:=by
    rw [hphys]
    exact cofiniteTangential_foot_mem_side θ d hθ hd hb j
  exact cofiniteTangential_self_foot_nonvertex θ d hθ hd hb hf ρ hθρ i hi
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q hf hne
      (cofiniteTangential_foot_mem_side θ d hθ hd hb i) hside)

/-- A genuine self-side center is in none of the actual original vertex orbits. -/
theorem cofiniteTangential_self_foot_not_vertex_orbit (i k:Fin n) (hi:ρ i=i)
    (g:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated) :
    g.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)))≠
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf k := by
  intro he
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))
  let p:P.Point:=⟨w,P.side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i)
    (cofiniteTangential_foot_mem_side θ d hθ hd hb i)⟩
  have hA:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q hf S
    (cofiniteTangential_opposite_side_neighborhoods θ d hθ hd hb hf ρ hρ hθρ)
    (cofiniteTangential_canonical_cycle_conditions θ d hθ hd hb hf ρ hρ hθρ hPeriod)
  have hEval:Function.Injective S.evaluation:=
    (hA.covering_homeomorph_of_compact S
      (S.native_metric_assumptions (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q hf)
        (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q hf))
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf).le (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf)).2.injective
  have hp:S.project (g,p)=S.project (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf k):=by apply hEval;exact he
  obtain ⟨N,hN,hret,hθk⟩:=hPeriod k
  have hm:(g,p)∈S.project ⁻¹' {S.project (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf k)}:=hp
  rw [cofiniteTangentialCanonicalWord_whole_fiber θ d hθ hd hb hf ρ hρ hθρ k N (by omega) hret hθk] at hm
  obtain ⟨j,hj⟩:=hm
  exact cofiniteTangential_self_foot_nonvertex θ d hθ hd hb hf ρ hθρ i hi
    ⟨_,congrArg (fun b:S.Copy=>b.2.val) hj⟩


/-- No unlisted nontrivial stabilizer occurs in the actual closed polygon. -/
theorem cofiniteTangential_carrier_nontrivial_fixed_point
    (x:ℍ) (hx:x∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf).carrier)
    (g:(cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ).Generated)
    (hg:g≠1) (hfix:g.val x=x) :
    x∈range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf) ∨
      ∃i:Fin n,ρ i=i ∧ x=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
  by_cases hv:x∈range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf)
  · exact Or.inl hv
  apply Or.inr
  rcases hx with hx|hx
  · have hA:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q hf S
      (cofiniteTangential_opposite_side_neighborhoods θ d hθ hd hb hf ρ hρ hθρ)
      (cofiniteTangential_canonical_cycle_conditions θ d hθ hd hb hf ρ hρ hθρ hPeriod)
    have hEval:Function.Injective S.evaluation:=
      (hA.covering_homeomorph_of_compact S
        (S.native_metric_assumptions (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q hf)
          (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q hf))
        (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf).le (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf)).2.injective
    let p:P.Point:=⟨x,P.interior_subset_carrier hx⟩
    have hp:S.project (g,p)=S.project (1,p):=by apply hEval;exact hfix
    have hm:(g,p)∈S.project ⁻¹' {S.project (1,p)}:=hp
    rw [S.project_fiber_eq_singleton_of_interior (1,p) hx] at hm
    exact False.elim (hg (congrArg Prod.fst hm))
  · obtain ⟨t,⟨i,rfl⟩,hi⟩:=mem_sUnion.mp hx
    obtain ⟨hself,hcenter,_⟩:=cofiniteTangential_side_nonvertex_fixed_center θ d hθ hd hb hf
      ρ hρ hθρ hPeriod i x hi hv g hg hfix
    exact ⟨i,hself,hcenter⟩

end ActualConeOrbits
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

section PrescribedConePoints
variable (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>
      (cofiniteConstructionAngles g ms last)[i]) d=Real.pi)

/-- Each original prescribed finite mark denotes its actual physical center;
order-two occurrences use their original self-side contact points. -/
def cofiniteConstructionConePoint : Option (Fin ms.length)→ℍ
  | none=>cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
      (cofiniteConstructionConeIndex g ms last hdef none)
  | some j=>if hj:ms[j]=2 then
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot
        (fun i:Fin (cofiniteConstructionAngles g ms last).length=>(cofiniteConstructionAngles g ms last)[i])
        d hd (finRotate _ (cofiniteConstructionSelfSideIndex g ms last ⟨j,hj⟩)))
    else cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
      (cofiniteConstructionConeIndex g ms last hdef (some ⟨j,hj⟩))

/-- The actual whole-group stabilizer of every prescribed physical cone point
has its exact original order, including repeated two marks. -/
theorem cofiniteConstruction_conePoint_stabilizer_card (i:Option (Fin ms.length)) :
    Nat.card (MulAction.stabilizer
      (cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated
      (cofiniteConstructionConePoint g ms last hms hlast hdef d hd hb i))=
        i.elim last (fun j=>ms[j]) := by
  cases i with
  | none=>exact cofiniteConstruction_base_stabilizer_card g ms last hms hlast hdef d hd hb _
  | some j=>
    dsimp only [cofiniteConstructionConePoint,Option.elim]
    by_cases hj:ms[j]=2
    · rw [dite_eq_left hj,hj]
      let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
      let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
        (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
      let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
        (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
      exact cofiniteTangential_self_foot_stabilizer_card θ d hθ hd hb hf
        (cofiniteConstructionPairing g ms last) (cofiniteConstructionPairing_involutive g ms last)
        (cofiniteConstructionPairing_angle_profile g ms last)
        (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef) _
        (cofiniteConstructionSelfSideIndex_fixed g ms last ⟨j,hj⟩)
    · rw [dite_eq_right hj]
      exact cofiniteConstruction_outer_stabilizer_card g ms last hms hlast hdef d hd hb ⟨j,hj⟩

/-- Numerical coincidences between prescribed cone orders do not identify
their actual whole-group orbits. -/
theorem cofiniteConstruction_conePoint_orbits_distinct (i j:Option (Fin ms.length))
    (k:(cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated)
    (he:k.val (cofiniteConstructionConePoint g ms last hms hlast hdef d hd hb i)=
      cofiniteConstructionConePoint g ms last hms hlast hdef d hd hb j) :i=j := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let ρ:=cofiniteConstructionPairing g ms last
  have hρ:=cofiniteConstructionPairing_involutive g ms last
  have hθρ:=cofiniteConstructionPairing_angle_profile g ms last
  have hPeriod:=cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef
  have hvertices (a b:Option {j:Fin ms.length //ms[j]≠2})
      (he':k.val (cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
        (cofiniteConstructionConeIndex g ms last hdef a))=
        cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
          (cofiniteConstructionConeIndex g ms last hdef b)):a=b:=
    cofiniteConstruction_vertex_representatives_distinct g ms last hms hlast hdef d hd hb a b ⟨k,he'⟩
  have hcross (a:{j:Fin ms.length //ms[j]=2}) (b:Fin (cofiniteConstructionAngles g ms last).length)
      (f:(cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated):
      f.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd
        (finRotate _ (cofiniteConstructionSelfSideIndex g ms last a))))≠
          cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb b:=
    cofiniteTangential_self_foot_not_vertex_orbit θ d hθ hd hb hf ρ hρ hθρ hPeriod _ b
      (cofiniteConstructionSelfSideIndex_fixed g ms last a) f
  cases i with
  | none=>
    cases j with
    | none=>rfl
    | some b=>
      dsimp only [cofiniteConstructionConePoint] at he
      split_ifs at he with hb2
      · have hinv:(k⁻¹).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd
            (finRotate _ (cofiniteConstructionSelfSideIndex g ms last ⟨b,hb2⟩))))=
              cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
                (cofiniteConstructionConeIndex g ms last hdef none):=by
          rw [←he];exact k.val.symm_apply_apply _
        exact False.elim (hcross ⟨b,hb2⟩ _ k⁻¹ hinv)
      · have hx:=hvertices none (some ⟨b,hb2⟩) he
        cases hx
  | some a=>
    cases j with
    | none=>
      dsimp only [cofiniteConstructionConePoint] at he
      split_ifs at he with ha2
      · exact False.elim (hcross ⟨a,ha2⟩ _ k he)
      · have hx:=hvertices (some ⟨a,ha2⟩) none he
        cases hx
    | some b=>
      dsimp only [cofiniteConstructionConePoint] at he
      split_ifs at he with ha2 hb2 hb2
      · have hlabels:=cofiniteTangential_self_foot_orbits_distinct θ d hθ hd hb hf ρ hρ hθρ hPeriod
          _ _ (cofiniteConstructionSelfSideIndex_fixed g ms last ⟨a,ha2⟩)
          (cofiniteConstructionSelfSideIndex_fixed g ms last ⟨b,hb2⟩) k he
        exact congrArg Option.some (congrArg Subtype.val
          (cofiniteConstructionSelfSideIndex_injective g ms last hlabels))
      · exact False.elim (hcross ⟨a,ha2⟩ _ k he)
      · have hinv:(k⁻¹).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd
            (finRotate _ (cofiniteConstructionSelfSideIndex g ms last ⟨b,hb2⟩))))=
              cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
                (cofiniteConstructionConeIndex g ms last hdef (some ⟨a,ha2⟩)):=by
          rw [←he];exact k.val.symm_apply_apply _
        exact False.elim (hcross ⟨b,hb2⟩ _ k⁻¹ hinv)
      · have hx:=hvertices (some ⟨a,ha2⟩) (some ⟨b,hb2⟩) he
        exact congrArg Option.some (congrArg Subtype.val (Option.some.inj hx))


/-- Every nontrivial stabilizer in the actual whole plane is conjugate to one
of the prescribed physical cone points. Closed-domain covering is derived
from the genuine construction, rather than supplied as a new premise. -/
theorem cofiniteConstruction_fixed_point_cone_orbit (x:ℍ)
    (a:(cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated)
    (ha:a≠1) (hfix:a.val x=x) :
    ∃i:Option (Fin ms.length),∃k:(cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated,
      k.val (cofiniteConstructionConePoint g ms last hms hlast hdef d hd hb i)=x := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let ρ:=cofiniteConstructionPairing g ms last
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb
  have hFD:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume P.interior:=
    (cofiniteConstruction_finite_poincare g ms last hms hlast hdef d hd hb).2
  obtain ⟨k,y,hy,hky⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.closure_covering S.Generated ℍ hFD x
  change k.val y=x at hky
  have hyP:y∈P.carrier:=(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf).symm ▸ hy
  let b:S.Generated:=k⁻¹*a*k
  have hbfix:b.val y=y:=by
    change k.val⁻¹ (a.val (k.val y))=y
    rw [hky,hfix,←hky]
    exact k.val.symm_apply_apply y
  have hbn:b≠1:=by
    intro he
    apply ha
    calc
      a=k*b*k⁻¹:=by dsimp only [b];group
      _=1:=by rw [he];group
  rcases cofiniteTangential_carrier_nontrivial_fixed_point θ d hθ hd hb hf ρ
      (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
      (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef) y hyP b hbn hbfix
      with ⟨i,hi⟩|⟨i,hself,hi⟩
  · have hi':cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb i=y:=hi
    obtain ⟨c,f,hf⟩:=cofiniteConstruction_vertex_representative_cover g ms last hms hlast hdef d hd hb i
    cases c with
    | none=>
      refine ⟨none,k*f,?_⟩
      change k.val (f.val (cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
        (cofiniteConstructionConeIndex g ms last hdef none)))=x
      rw [hf,hi',hky]
    | some c=>
      refine ⟨some c.val,k*f,?_⟩
      dsimp only [cofiniteConstructionConePoint]
      rw [dite_eq_right c.property]
      change k.val (f.val (cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb
        (cofiniteConstructionConeIndex g ms last hdef (some c))))=x
      rw [hf,hi',hky]
  · obtain ⟨j,hj⟩:=(cofiniteConstructionPairing_fixed_iff g ms last i).mp hself
    refine ⟨some j.val,k,?_⟩
    dsimp only [cofiniteConstructionConePoint]
    rw [dite_eq_left j.property]
    rw [hj,←hi]
    exact hky

end PrescribedConePoints
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

section ActualPrescribedClasses
variable (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>
      (cofiniteConstructionAngles g ms last)[i]) d=Real.pi)

/-- The actual faithful whole Mobius image, retaining the original side generators. -/
def cofiniteConstructionFiniteMobiusGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  cofiniteTangentialMobiusGroup θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)

/-- The actual original projective whole group supplied by the construction. -/
theorem cofiniteConstructionFiniteHalfPlaneData :
    HalfPlaneFuchsianGroup (cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb) :=
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  cofiniteTangentialHalfPlaneData θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
    (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef)

/-- Faithful identification with the actual Cayley-disc group, not an abstract presentation. -/
def cofiniteConstructionFiniteCayleyEquiv :
    (cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated ≃*
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
        (cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb) :=
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  (cofiniteTangentialGroupEquiv θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)).trans
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
        (cofiniteTangentialMobiusGroup θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
          (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)))

theorem cofiniteConstructionFiniteCayleyEquiv_action
    (a:(cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated) (x:ℍ) :
    (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyCoordinate (a.val x)=
      cofiniteConstructionFiniteCayleyEquiv g ms last hms hlast hdef d hd hb a •
        (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyCoordinate x := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let P:=cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb
  have he:=P.cayleyCoordinate_equivariant
    (cofiniteTangentialGroupEquiv θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
      (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last) a) x
  rw [cofiniteTangentialGroupEquiv_action θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
    (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef)] at he
  exact he

/-- Every prescribed physical point is an actual elliptic fixed point of
the entire constructed original group. -/
theorem cofiniteConstruction_conePoint_elliptic (i:Option (Fin ms.length)) :
    ((cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyCoordinate
      (cofiniteConstructionConePoint g ms last hms hlast hdef d hd hb i)).val∈
        fuchsianCyclicFixedPoints
          (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc .elliptic := by
  let S:=cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb
  let P:=cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb
  let E:=cofiniteConstructionFiniteCayleyEquiv g ms last hms hlast hdef d hd hb
  let z:=cofiniteConstructionConePoint g ms last hms hlast hdef d hd hb i
  have hcard:2≤Nat.card (MulAction.stabilizer S.Generated z):=by
    rw [cofiniteConstruction_conePoint_stabilizer_card]
    cases i with
    | none=>exact hlast
    | some j=>exact hms _ (List.getElem_mem j.isLt)
  let :Finite (MulAction.stabilizer S.Generated z):=Nat.finite_of_card_ne_zero (by omega)
  let :Nontrivial (MulAction.stabilizer S.Generated z):=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,ha⟩:=exists_ne (1:MulAction.stabilizer S.Generated z)
  have han:a.val≠1:=fun he=>ha (Subtype.ext he)
  have hn:(E a.val).val≠1:=by
    intro he
    apply han
    apply E.injective
    exact (Subtype.ext he).trans E.map_one.symm
  have hfix:(E a.val).val.val (P.cayleyCoordinate z).val=(P.cayleyCoordinate z).val:=by
    have hact:=cofiniteConstructionFiniteCayleyEquiv_action g ms last hms hlast hdef d hd hb a.val z
    rw [show a.val.val z=z from a.property] at hact
    exact (congrArg Subtype.val hact).symm
  have hp:(P.cayleyCoordinate z).val∈P.cayleyData.asFuchsianDisc.carrier:=(P.cayleyCoordinate z).property
  exact ⟨fun _=>hp,(E a.val).val,(E a.val).property,
    fuchsianDisc_nonidentity_fixed_elliptic P.cayleyData.asFuchsianDisc _ (E a.val).property hn _ hp hfix,hfix⟩

def cofiniteConstructionEllipticPoint (i:Option (Fin ms.length)) :
    fuchsianCyclicFixedPoints
      (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc .elliptic :=
  ⟨((cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyCoordinate
    (cofiniteConstructionConePoint g ms last hms hlast hdef d hd hb i)).val,
    cofiniteConstruction_conePoint_elliptic g ms last hms hlast hdef d hd hb i⟩


/-- All elliptic fixed-point orbits of the actual original group are exhausted. -/
theorem cofiniteConstruction_elliptic_point_cone_orbit
    (p:fuchsianCyclicFixedPoints
      (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc .elliptic) :
    ∃i:Option (Fin ms.length),∃a:
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
        (cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb),
      a • p=cofiniteConstructionEllipticPoint g ms last hms hlast hdef d hd hb i := by
  let P:=cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb
  let E:=cofiniteConstructionFiniteCayleyEquiv g ms last hms hlast hdef d hd hb
  let z:=P.cayleyCoordinate.symm ⟨p.val,p.property.1 rfl⟩
  have hz:(P.cayleyCoordinate z).val=p.val:=congrArg Subtype.val
    (P.cayleyCoordinate.apply_symm_apply ⟨p.val,p.property.1 rfl⟩)
  obtain ⟨f,hfH,hf,hfix⟩:=p.property.2
  let a:=E.symm ⟨f,hfH⟩
  have he:(E a).val=f:=congrArg Subtype.val (E.apply_symm_apply ⟨f,hfH⟩)
  have hfix':a.val z=z:=by
    apply P.cayleyCoordinate.injective
    rw [cofiniteConstructionFiniteCayleyEquiv_action]
    apply Subtype.ext
    change (E a).val.val (P.cayleyCoordinate z).val=(P.cayleyCoordinate z).val
    rw [he,hz,hfix]
  have han:a≠1:=by
    intro h
    rw [h,E.map_one] at he
    exact hf.1 he.symm
  obtain ⟨i,k,hk⟩:=cofiniteConstruction_fixed_point_cone_orbit g ms last hms hlast hdef d hd hb z a han hfix'
  have hki:(k⁻¹).val z=cofiniteConstructionConePoint g ms last hms hlast hdef d hd hb i:=by
    rw [←hk];exact k.val.symm_apply_apply _
  refine ⟨i,E k⁻¹,Subtype.ext ?_⟩
  change (E k⁻¹).val.val p.val=(P.cayleyCoordinate
    (cofiniteConstructionConePoint g ms last hms hlast hdef d hd hb i)).val
  rw [←hz]
  have hact:=cofiniteConstructionFiniteCayleyEquiv_action g ms last hms hlast hdef d hd hb k⁻¹ z
  exact (congrArg Subtype.val hact).symm.trans (congrArg (fun t=>(P.cayleyCoordinate t).val) hki)

/-- The original occurrence labels remain distinct in the full original group. -/
theorem cofiniteConstruction_elliptic_point_orbits_distinct (i j:Option (Fin ms.length))
    (a:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
        (cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb))
    (h:a • cofiniteConstructionEllipticPoint g ms last hms hlast hdef d hd hb i=
      cofiniteConstructionEllipticPoint g ms last hms hlast hdef d hd hb j):i=j := by
  let P:=cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb
  let E:=cofiniteConstructionFiniteCayleyEquiv g ms last hms hlast hdef d hd hb
  apply cofiniteConstruction_conePoint_orbits_distinct g ms last hms hlast hdef d hd hb i j (E.symm a)
  apply P.cayleyCoordinate.injective
  rw [cofiniteConstructionFiniteCayleyEquiv_action,E.apply_symm_apply]
  have hv:=congrArg (fun p:fuchsianCyclicFixedPoints P.cayleyData.asFuchsianDisc .elliptic=>p.val) h
  exact Subtype.ext hv


/-- The actual orbit class of each independently labelled physical mark. -/
def cofiniteConstructionEllipticPointClass (i:Option (Fin ms.length)) :
    MulAction.orbitRel.Quotient
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb))
      (fuchsianCyclicFixedPoints
        (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc .elliptic):=
  Quotient.mk'' (cofiniteConstructionEllipticPoint g ms last hms hlast hdef d hd hb i)

theorem cofiniteConstructionEllipticPointClass_bijective :
    Function.Bijective (cofiniteConstructionEllipticPointClass g ms last hms hlast hdef d hd hb) := by
  constructor
  · intro i j he
    obtain ⟨a,ha⟩:=MulAction.mem_orbit_iff.mp (Quotient.exact he)
    exact (cofiniteConstruction_elliptic_point_orbits_distinct g ms last hms hlast hdef d hd hb j i a ha).symm
  · intro q
    induction q using Quotient.inductionOn' with
    | h p=>
      obtain ⟨i,a,ha⟩:=cofiniteConstruction_elliptic_point_cone_orbit g ms last hms hlast hdef d hd hb p
      exact ⟨i,Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨a,ha⟩)⟩

/-- Every prescribed occurrence is exactly one actual maximal elliptic
subgroup conjugacy class of the constructed whole original group. -/
def cofiniteConstructionEllipticClassEquiv :
    Option (Fin ms.length)≃FuchsianCyclicConjugacyClasses
      (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc .elliptic :=
  (Equiv.ofBijective (cofiniteConstructionEllipticPointClass g ms last hms hlast hdef d hd hb)
    (cofiniteConstructionEllipticPointClass_bijective g ms last hms hlast hdef d hd hb)).trans
      (fuchsianCyclicConjugacyClassesEquiv
        (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc .elliptic).symm

/-- The actual maximal elliptic classes have precisely the original ordered
mark values; none is replaced by a mere lower bound on stabilizer order. -/
theorem cofiniteConstructionEllipticClassEquiv_order (i:Option (Fin ms.length)) :
    fuchsianEllipticClassOrder
      (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc
      (cofiniteConstructionEllipticClassEquiv g ms last hms hlast hdef d hd hb i)=
        i.elim last (fun j=>ms[j]) := by
  let P:=cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb
  let z:=cofiniteConstructionConePoint g ms last hms hlast hdef d hd hb i
  change fuchsianEllipticClassOrder P.cayleyData.asFuchsianDisc
    (Quotient.mk _ (fuchsianCyclicPointStabilizer P.cayleyData.asFuchsianDisc .elliptic
      (cofiniteConstructionEllipticPoint g ms last hms hlast hdef d hd hb i)))=_
  rw [fuchsianEllipticClassOrder_mk]
  change Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb))
    (P.cayleyCoordinate z).val)=_
  rw [←Nat.card_congr (P.cayleyData.stabilizerEquivBoundary (P.cayleyCoordinate z)).toEquiv]
  change fuchsianPointOrder P.cayleyData (P.cayleyCoordinate z)=_
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  rw [cofiniteTangential_projective_disc_pointOrder θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
    (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef)]
  exact cofiniteConstruction_conePoint_stabilizer_card g ms last hms hlast hdef d hd hb i

end ActualPrescribedClasses
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open MeasureTheory
local instance cofiniteSignatureSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance cofiniteSignatureSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

section ActualFiniteSignature
variable (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>
      (cofiniteConstructionAngles g ms last)[i]) d=Real.pi)

/-- The physical original fundamental domain, with no change of source points. -/
def cofiniteConstructionFiniteDiscDomain :
    Set (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.domain.carrier :=
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyCoordinate ''
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior)

/-- Every actual finite elliptic class is counted with its original multiplicity. -/
theorem cofiniteConstruction_elliptic_orders_perm
    [Finite (FuchsianCyclicConjugacyClasses
      (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc .elliptic)] :
    (ms++[last]).Perm (fuchsianEllipticOrderList
      (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc) := by
  classical
  let D:=(cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc
  let :=Fintype.ofFinite (FuchsianCyclicConjugacyClasses D .elliptic)
  let e:=(finSuccEquivLast (n:=ms.length)).trans
    ((cofiniteConstructionEllipticClassEquiv g ms last hms hlast hdef d hd hb).trans
      (Fintype.equivFin (FuchsianCyclicConjugacyClasses D .elliptic)))
  let v:Fin (ms.length+1)→ℕ:=fun i=>(finSuccEquivLast i).elim last (fun j=>ms[j])
  have hv:List.ofFn v=ms++[last]:=by
    rw [List.ofFn_succ']
    simp only [v,finSuccEquivLast_castSucc,finSuccEquivLast_last,Option.elim_some,
      Option.elim_none,List.concat_eq_append]
    change (List.ofFn (fun i:Fin ms.length=>ms[i.val]))++[last]=ms++[last]
    rw [List.ofFn_getElem]
  rw [←hv]
  apply signature_orderList_perm_of_equiv e
  intro i
  simp only [e,Equiv.trans_apply]
  change fuchsianEllipticClassOrder D
    ((Fintype.equivFin (FuchsianCyclicConjugacyClasses D .elliptic)).symm
      ((Fintype.equivFin (FuchsianCyclicConjugacyClasses D .elliptic))
        ((cofiniteConstructionEllipticClassEquiv g ms last hms hlast hdef d hd hb) (finSuccEquivLast i))))=v i
  rw [Equiv.symm_apply_apply]
  exact cofiniteConstructionEllipticClassEquiv_order g ms last hms hlast hdef d hd hb _

/-- The original physical hyperbolic area is exactly the prescribed signature deficit. -/
theorem cofiniteConstruction_physical_area :
    (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.area
      (cofiniteConstructionFiniteDiscDomain g ms last hms hlast hdef d hd hb)=
        ENNReal.ofReal (2*Real.pi*cofiniteConstructionDeficit g ms last) := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  dsimp only [cofiniteConstructionFiniteDiscDomain]
  rw [cofiniteTangential_projective_disc_area_exact θ d hθ hd hb hf
    (cofiniteConstructionPairing g ms last) (cofiniteConstructionPairing_involutive g ms last)
    (cofiniteConstructionPairing_angle_profile g ms last)
    (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef)]
  congr 1
  have hs:∑i:Fin (cofiniteConstructionAngles g ms last).length,θ i=
      (cofiniteConstructionAngles g ms last).sum:=by
    change (∑i:Fin (cofiniteConstructionAngles g ms last).length,
      (cofiniteConstructionAngles g ms last)[i.val])=(cofiniteConstructionAngles g ms last).sum
    rw [←List.sum_ofFn,List.ofFn_getElem]
  rw [hs]
  exact cofiniteConstruction_angles_defect g ms last
    (lt_of_lt_of_le (by decide:0<2) (cofiniteConstruction_base_count g ms last hdef))

/-- Compactness of the unchanged finite polygon excludes every actual parabolic element. -/
theorem cofiniteConstruction_no_parabolic
    (f:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb)) :
    ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val := by
  intro hf
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hfin:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let ρ:=cofiniteConstructionPairing g ms last
  let hρ:=cofiniteConstructionPairing_involutive g ms last
  let hθρ:=cofiniteConstructionPairing_angle_profile g ms last
  let hPeriod:=cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef
  let P:=(cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData
  let D:=cofiniteConstructionFiniteDiscDomain g ms last hms hlast hdef d hd hb
  have hD:IsConvexFuchsianPolygon P D:=
    cofiniteTangential_projective_disc_convex θ d hθ hd hb hfin ρ hρ hθρ hPeriod
  obtain ⟨ξ,hξ⟩:=hf.2
  have hfix:f.val.val ξ=ξ:=(hξ ξ).mpr rfl
  have hfront:=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_fixed_mem_disc_frontier f.val hf _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc
    (P.image_eq f) hfix
  obtain ⟨a,ha⟩:=hD.locallyFinite.parabolic_fixedPoint_orbit_mem_closure f hf ξ hfix
  have hcompact:IsCompact ((Subtype.val:P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' closure D):=
    (cofiniteTangential_projective_disc_closure_compact θ d hθ hd hb hfin ρ hρ hθρ hPeriod).image continuous_subtype_val
  have hsub:closure ((Subtype.val:P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) ⊆
      (Subtype.val:P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' closure D:=
    closure_minimal (image_mono subset_closure) hcompact.isClosed
  obtain ⟨x,_hx,hxe⟩:=hsub ha
  have hin:ξ∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
    have hx':=P.invariant a⁻¹ x.val x.property
    change a⁻¹.val.val x.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at hx'
    have he:a⁻¹.val.val x.val=ξ:=by rw [hxe];exact a.val.val.symm_apply_apply ξ
    rwa [he] at hx'
  exact hfront.2 (by rwa [_root_.LowDimensionalTopology.Geometry.Mobius.isOpen_extendedUnitDisc.interior_eq])

/-- The construction has its actual prescribed cofinite signature, with genus
identified by genuine quotient-area and actual elliptic subgroup classes. -/
theorem cofiniteConstruction_finite_actual_signature :
    HasCofiniteFuchsianSignature
      (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc
        g (ms++[last]) 0 := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let ρ:=cofiniteConstructionPairing g ms last
  let hρ:=cofiniteConstructionPairing_involutive g ms last
  let hθρ:=cofiniteConstructionPairing_angle_profile g ms last
  let hPeriod:=cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef
  let P:=(cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData
  let D:=cofiniteConstructionFiniteDiscDomain g ms last hms hlast hdef d hd hb
  have hFD:IsFuchsianFundamentalDomain P D:=
    cofiniteTangential_projective_disc_fundamental θ d hθ hd hb hf ρ hρ hθρ hPeriod
  have ha:P.area D≠⊤:=by rw [cofiniteConstruction_physical_area];exact ENNReal.ofReal_ne_top
  obtain ⟨s,hbnd,hSig,harea⟩:=finite_area_unitDisc_signature_area P D hFD ha
  let :=hSig.ellipticClassesFinite
  have horders:s.ellipticOrders.Perm (ms++[last]):=
    hSig.ellipticOrders.trans (cofiniteConstruction_elliptic_orders_perm g ms last hms hlast hdef d hd hb).symm
  have hP:IsEmpty (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic):=
    (fuchsianCyclicConjugacyClasses_isEmpty_iff P.asFuchsianDisc .parabolic).mpr
      (fun f hf=>cofiniteConstruction_no_parabolic g ms last hms hlast hdef d hd hb ⟨f,hf⟩)
  have hcusps:s.parabolicEnds=0:=hSig.cuspCount.trans (@Nat.card_of_isEmpty _ hP)
  have hnonneg:0≤2*Real.pi*cofiniteConstructionDeficit g ms last:=by positivity
  rw [cofiniteConstruction_physical_area,ENNReal.toReal_ofReal hnonneg] at harea
  have hlen:=horders.length_eq
  have hsum:((s.ellipticOrders.map (fun m:ℕ=>(1:ℝ)/m)).sum)=
      (ms.map (fun m:ℕ=>(1:ℝ)/m)).sum+1/(last:ℝ):=by
    rw [(horders.map _).sum_eq,List.map_append,List.sum_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  simp only [FuchsianSignature.deficit,hcusps,hbnd,Nat.cast_zero,add_zero] at harea
  have hsubsum (ls:List ℕ):
      (ls.map (fun m:ℕ=>(1:ℝ)-1/m)).sum=(ls.length:ℝ)-(ls.map (fun m:ℕ=>(1:ℝ)/m)).sum:=by
    induction ls with
    | nil=>simp
    | cons m ls ih=>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      rw [ih]
      ring
  rw [hsubsum,hsum] at harea
  simp only [List.length_append,List.length_cons,List.length_nil,zero_add] at hlen
  rw [hlen] at harea
  have hgenus:(s.genus:ℝ)=g:=by
    dsimp only [cofiniteConstructionDeficit] at harea
    push_cast at harea
    nlinarith [Real.pi_pos]
  have hg:s.genus=g:=by exact_mod_cast hgenus
  exact {
    ellipticClassesFinite:=hSig.ellipticClassesFinite
    parabolicClassesFinite:=hSig.parabolicClassesFinite
    compact:=hSig.compact
    topologicalGenus:=hg ▸ hSig.topologicalGenus
    ellipticOrders:=horders.symm.trans hSig.ellipticOrders
    cuspCount:=hcusps ▸ hSig.cuspCount}

end ActualFiniteSignature
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

section OriginalSides
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (hf:∀i,‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
include hPeriod
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "S₀" => cofiniteTangentialFiniteSidePairing θ d hθ hd hb hf ρ hρ hθρ
local notation "P₀" => cofiniteTangentialHalfPlaneData θ d hθ hd hb hf ρ hρ hθρ hPeriod
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => f₀ '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q₀)
local notation "E₀" => MulEquiv.trans (cofiniteTangentialGroupEquiv θ d hθ hd hb hf ρ hρ hθρ)
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteTangentialMobiusGroup θ d hθ hd hb hf ρ hρ hθρ))
local notation "hD₀" => cofiniteTangential_projective_disc_convex θ d hθ hd hb hf ρ hρ hθρ hPeriod

/-- The full original group acts by the same physical maps in the genuine Cayley coordinate. -/
theorem cofiniteTangential_original_coordinate_action (g:(S₀).Generated) (z:ℍ) :
    f₀ (g.val z)=E₀ g • f₀ z := by
  have h:=(P₀).cayleyCoordinate_equivariant
    (cofiniteTangentialGroupEquiv θ d hθ hd hb hf ρ hρ hθρ g) z
  rw [cofiniteTangentialGroupEquiv_action θ d hθ hd hb hf ρ hρ hθρ hPeriod] at h
  exact h

/-- Actual complete natural cycles give the true injective developing evaluation. -/
theorem cofiniteTangential_actual_evaluation_injective : Function.Injective (S₀).evaluation := by
  let generatedIsometric:IsIsometricSMul (S₀).Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hA:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q₀ hf S₀
    (cofiniteTangential_opposite_side_neighborhoods θ d hθ hd hb hf ρ hρ hθρ)
    (cofiniteTangential_canonical_cycle_conditions θ d hθ hd hb hf ρ hρ hθρ hPeriod)
  exact (hA.covering_homeomorph_of_compact S₀
    ((S₀).native_metric_assumptions (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q₀ hf)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q₀ hf))
    (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q₀ hf).le (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q₀ hf)).2.injective

/-- Every whole-group closed-tile incidence at a nonvertex is the identity or its unique original side crossing. -/
theorem cofiniteTangential_nonvertex_closed_incidence (x:ℍ)
    (hx:x∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q₀ hf).carrier)
    (hv:x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₀ hf)) (g:(S₀).Generated) (y:ℍ)
    (hy:y∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q₀ hf).carrier) (hgy:g.val y=x) :
    g=1 ∨ ∃i:Fin n,x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i ∧ g=((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf i))⁻¹ := by
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q₀ hf
  let S:=S₀
  let p:P.Point:=⟨x,hx⟩
  let q:P.Point:=⟨y,hy⟩
  have hproj:S.project (g,q)=S.project (1,p):=by
    apply cofiniteTangential_actual_evaluation_injective θ d hθ hd hb hf ρ hρ hθρ hPeriod
    exact hgy
  have hm:(g,q)∈S.project ⁻¹' {S.project (1,p)}:=hproj
  by_cases hI:x∈P.interior
  · rw [S.project_fiber_eq_singleton_of_interior (1,p) hI] at hm
    exact Or.inl (congrArg Prod.fst hm)
  · have hB:x∈P.boundary:=hx.resolve_left hI
    obtain ⟨_,⟨i,rfl⟩,hi⟩:=mem_sUnion.mp hB
    let s:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf i
    have hmate:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_pairing_nonvertex Q₀ hf S i hi hv
    have hu:∀t:P.Side,x∈t.val→t=s:=by
      intro t ht
      obtain ⟨j,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf).surjective t
      by_cases he:i=j
      · exact congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf) he.symm
      · exact (hv (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q₀ hf he hi ht)).elim
    have hw:∀t:P.Side,(S.sideMateCopy (1,p) s hi).2.val∈t.val→t=S.paired s:=by
      intro t ht
      let v:=S.generator s • x
      have hvp:v∈(S.paired s).val:=by rw [←S.generator_side_image];exact ⟨x,hi,rfl⟩
      obtain ⟨j,hj⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf).surjective (S.paired s)
      obtain ⟨l,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf).surjective t
      by_cases he:j=l
      · exact (congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf) he.symm).trans hj
      · have hvj:v∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ j:=by change v∈((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf) j).val;rw [hj];exact hvp
        exact (hmate (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q₀ hf he hvj ht)).elim
    rw [S.project_fiber_eq_side_pair (1,p) s hi hu hw] at hm
    rcases hm with he|he
    · exact Or.inl (congrArg Prod.fst he)
    · exact Or.inr ⟨i,hi,by simpa only [_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.sideMateCopy,one_mul] using congrArg Prod.fst he⟩

/-- The literal closed native carrier maps exactly to the original domain closure. -/
theorem cofiniteTangential_original_carrier_image :
    f₀ '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q₀ hf).carrier=closure D₀ := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q₀ hf]
  exact (f₀).image_closure _

/-- The actual original side is the true intersection with the inverse-pairing neighbor. -/
theorem cofiniteTangential_original_side_intersection (i:Fin n) :
    f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i=closure D₀ ∩
      fuchsianDomainTile (P₀).cayleyData D₀ (E₀ (((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf i))⁻¹)) := by
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q₀ hf
  let g:=(S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf i)
  have hcut:P.carrier∩g.val ⁻¹' P.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i:=by
    change P.carrier∩(S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf i) ⁻¹' P.carrier=_
    rw [cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ i]
    exact cofiniteTangentPairing_carrier_intersection θ d hθ hd hb hf i (ρ i)
      (hθρ i) (cofiniteTangentialPairing_other_angle θ ρ hρ hθρ i)
  change f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i=closure D₀ ∩ (fun z=>E₀ g⁻¹ • z) '' closure D₀
  rw [←cofiniteTangential_original_carrier_image θ d hθ hd hb hf ρ hρ hθρ hPeriod]
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hxP:x∈P.carrier∩g.val ⁻¹' P.carrier:=hcut.symm ▸ hx
    refine ⟨⟨x,hxP.1,rfl⟩,f₀ (g.val x),⟨g.val x,hxP.2,rfl⟩,?_⟩
    have he:=cofiniteTangential_original_coordinate_action θ d hθ hd hb hf ρ hρ hθρ hPeriod g⁻¹ (g.val x)
    exact he.symm.trans (congrArg f₀ (inv_smul_smul g x))
  · rintro ⟨⟨x,hx,rfl⟩,w,⟨y,hy,rfl⟩,he⟩
    have hyx:g⁻¹ • y=x:=(f₀).injective
      ((cofiniteTangential_original_coordinate_action θ d hθ hd hb hf ρ hρ hθρ hPeriod g⁻¹ y).trans he)
    have hxy:g.val x=y:=by rw [←hyx];exact smul_inv_smul g y
    refine ⟨x,hcut ▸ And.intro hx ?_,rfl⟩
    change g.val x∈P.carrier
    rwa [hxy]

omit hPeriod in
/-- No original side generator is the identity in the entire native group. -/
theorem cofiniteTangential_original_generator_ne_one (i:Fin n) :
    (S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf i)≠1 := by
  intro he
  have h:(S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf i)=1:=congrArg Subtype.val he
  rw [cofiniteTangentialSidePairing_element_index θ d hθ hd hb hf ρ hρ hθρ i] at h
  exact cofiniteTangentPairingElement_ne_one θ d hθ hd hb i (ρ i) h

/-- Each original labelled whole side is a genuine side of the actual Fuchsian polygon. -/
def cofiniteTangentialOriginalSide (i:Fin n) : FuchsianPolygonSides (P₀).cayleyData D₀ := by
  refine ⟨f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i,?_⟩
  have hn:(f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i).Nontrivial:=by
    have hbase:(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i).Nontrivial:=⟨_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₀ hf i,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_left_mem Q₀ hf i,
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₀ hf (finRotate n i),_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_right_mem Q₀ hf i,
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q₀ hf).ne ((Q₀).next_ne_self i).symm⟩
    exact hbase.image (f₀).injective
  rw [cofiniteTangential_original_side_intersection θ d hθ hd hb hf ρ hρ hθρ hPeriod i] at hn ⊢
  apply (hD₀).side_of_nontrivial_intersection ?_ hn
  intro he
  apply inv_ne_one.mpr (cofiniteTangential_original_generator_ne_one θ d hθ hd hb hf ρ hρ hθρ i)
  apply (E₀).injective
  exact he.trans (E₀).map_one.symm

theorem cofiniteTangentialOriginalSide_element (i:Fin n) :
    fuchsianSideElement hD₀ (cofiniteTangentialOriginalSide θ d hθ hd hb hf ρ hρ hθρ hPeriod i)=
      E₀ (((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf i))⁻¹) := by
  apply ((hD₀).existsUnique_side_element
    (cofiniteTangentialOriginalSide θ d hθ hd hb hf ρ hρ hθρ hPeriod i).property).unique
      (fuchsianSideElement_spec hD₀ _)
  constructor
  · intro he
    apply inv_ne_one.mpr (cofiniteTangential_original_generator_ne_one θ d hθ hd hb hf ρ hρ hθρ i)
    apply (E₀).injective
    exact he.trans (E₀).map_one.symm
  · exact cofiniteTangential_original_side_intersection θ d hθ hd hb hf ρ hρ hθρ hPeriod i

theorem cofiniteTangentialOriginalSide_injective :
    Function.Injective (cofiniteTangentialOriginalSide θ d hθ hd hb hf ρ hρ hθρ hPeriod) := by
  intro i j he
  apply _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_injective Q₀ hf
  exact (f₀).injective.image_injective (congrArg Subtype.val he)

/-- Actual positive-length sides cannot be hidden among the finitely many original vertices. -/
theorem cofiniteTangentialOriginalSide_surjective :
    Function.Surjective (cofiniteTangentialOriginalSide θ d hθ hd hb hf ρ hρ hθρ hPeriod) := by
  intro s
  let f:=f₀
  let E:=E₀
  let V:Set (P₀).cayleyData.domain.carrier:=range (fun i:Fin n=>f (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₀ hf i))
  have hV:V.Finite:=finite_range _
  let :T2Space (P₀).cayleyData.domain.carrier:=f.symm.isEmbedding.t2Space
  have hpre:IsPreconnected s.val:=
    (P₀).cayleyData.finiteCoordinate.isEmbedding.isInducing.isPreconnected_image.mp
      s.property.2.1.1.isPreconnected
  have hinf:s.val.Infinite:=hpre.infinite_of_nontrivial s.property.2.2
  have hex:∃z∈s.val,z∉V:=by
    by_contra he
    apply hinf
    apply hV.subset
    intro z hz
    by_contra hzV
    exact he ⟨z,hz,hzV⟩
  obtain ⟨z,hz,hzV⟩:=hex
  have hzC:z∈closure D₀:=((fuchsianSideElement_spec hD₀ s).2 ▸ hz).1
  rw [←cofiniteTangential_original_carrier_image θ d hθ hd hb hf ρ hρ hθρ hPeriod] at hzC
  obtain ⟨x,hx,rfl⟩:=hzC
  have hv:x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₀ hf):=by
    rintro ⟨i,rfl⟩
    exact hzV ⟨i,rfl⟩
  have hzT:f x∈fuchsianDomainTile (P₀).cayleyData D₀ (fuchsianSideElement hD₀ s):=
    ((fuchsianSideElement_spec hD₀ s).2 ▸ hz).2
  obtain ⟨w,hw,hew⟩:=hzT
  rw [←cofiniteTangential_original_carrier_image θ d hθ hd hb hf ρ hρ hθρ hPeriod] at hw
  obtain ⟨y,hy,rfl⟩:=hw
  let g:=E.symm (fuchsianSideElement hD₀ s)
  have hgy:g.val y=x:=by
    apply f.injective
    rw [cofiniteTangential_original_coordinate_action θ d hθ hd hb hf ρ hρ hθρ hPeriod,E.apply_symm_apply]
    exact hew
  rcases cofiniteTangential_nonvertex_closed_incidence θ d hθ hd hb hf ρ hρ hθρ hPeriod
      x hx hv g y hy hgy with he|⟨i,_hxi,he⟩
  · exact False.elim ((fuchsianSideElement_spec hD₀ s).1
      ((E.apply_symm_apply _).symm.trans ((congrArg E he).trans E.map_one)))
  · refine ⟨i,?_⟩
    apply fuchsianSideElement_injective hD₀
    rw [cofiniteTangentialOriginalSide_element θ d hθ hd hb hf ρ hρ hθρ hPeriod i]
    have h:=congrArg E he
    rw [E.apply_symm_apply] at h
    exact h.symm

/-- The original finite side labels enumerate all actual Fuchsian sides exactly once. -/
def cofiniteTangentialOriginalSideEquiv : Fin n ≃ FuchsianPolygonSides (P₀).cayleyData D₀ :=
  Equiv.ofBijective (cofiniteTangentialOriginalSide θ d hθ hd hb hf ρ hρ hθρ hPeriod)
    ⟨cofiniteTangentialOriginalSide_injective θ d hθ hd hb hf ρ hρ hθρ hPeriod,
      cofiniteTangentialOriginalSide_surjective θ d hθ hd hb hf ρ hρ hθρ hPeriod⟩

/-- Original actual side pairing is precisely the unchanged literal involution on its labels. -/
theorem cofiniteTangentialOriginalSide_paired (i:Fin n) :
    fuchsianPairedSide hD₀ (cofiniteTangentialOriginalSide θ d hθ hd hb hf ρ hρ hθρ hPeriod i)=
      cofiniteTangentialOriginalSide θ d hθ hd hb hf ρ hρ hθρ hPeriod (ρ i) := by
  apply fuchsianSideElement_injective hD₀
  rw [fuchsianSideElement_paired,
    cofiniteTangentialOriginalSide_element θ d hθ hd hb hf ρ hρ hθρ hPeriod i,
    cofiniteTangentialOriginalSide_element θ d hθ hd hb hf ρ hρ hθρ hPeriod (ρ i)]
  have hp:=(S₀).generator_paired (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q₀ hf i)
  rw [cofiniteTangentialSidePairing_paired_index θ d hθ hd hb hf ρ hρ hθρ i] at hp
  simp only [hp,map_inv,inv_inv]

/-- The actual self-paired sides retain exactly their original fixed occurrence labels. -/
def cofiniteTangentialOriginalSelfSideEquiv :
    {i:Fin n //ρ i=i} ≃ {s:FuchsianPolygonSides (P₀).cayleyData D₀ //fuchsianPairedSide hD₀ s=s} :=
  (cofiniteTangentialOriginalSideEquiv θ d hθ hd hb hf ρ hρ hθρ hPeriod).subtypeEquiv (fun i=>by
    change ρ i=i ↔ fuchsianPairedSide hD₀
      (cofiniteTangentialOriginalSide θ d hθ hd hb hf ρ hρ hθρ hPeriod i)=
        cofiniteTangentialOriginalSide θ d hθ hd hb hf ρ hρ hθρ hPeriod i
    rw [cofiniteTangentialOriginalSide_paired θ d hθ hd hb hf ρ hρ hθρ hPeriod i]
    exact (cofiniteTangentialOriginalSide_injective θ d hθ hd hb hf ρ hρ hθρ hPeriod).eq_iff.symm)

theorem cofiniteTangential_original_side_card : Nat.card (FuchsianPolygonSides (P₀).cayleyData D₀)=n := by
  rw [←Nat.card_congr (cofiniteTangentialOriginalSideEquiv θ d hθ hd hb hf ρ hρ hθρ hPeriod)]
  exact Nat.card_fin n

/-- Subdividing each true self-side once gives exactly raw sides plus actual fixed labels. -/
theorem cofiniteTangential_original_refined_side_card :
    Nat.card (OriginalRefinedSide hD₀)=n+Nat.card {i:Fin n //ρ i=i} := by
  rw [originalRefinedSide_card hD₀
    (ne_of_lt (cofiniteTangential_projective_disc_area_lt_top θ d hθ hd hb hf ρ hρ hθρ hPeriod)),
    cofiniteTangential_original_side_card θ d hθ hd hb hf ρ hρ hθρ hPeriod,
    ←Nat.card_congr (cofiniteTangentialOriginalSelfSideEquiv θ d hθ hd hb hf ρ hρ hθρ hPeriod)]

end OriginalSides

/-- The finite occurrence subtype counts every entry equal to two, with multiplicity. -/
theorem cofiniteConstruction_order_two_occurrence_card (ms:List ℕ) :
    Nat.card {j:Fin ms.length //ms[j]=2}=ms.count 2 := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact Fin.card_filter_univ_eq_vector_get_eq_count 2 ⟨ms,rfl⟩

/-- Every admissible actual finite construction attains its exact refined original side count. -/
theorem cofiniteConstruction_actual_refined_side_count (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last) (hdef:0<cofiniteConstructionDeficit g ms last)
    (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i=>(cofiniteConstructionAngles g ms last)[i]) d=Real.pi) :
    let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=
      fun i=>(cofiniteConstructionAngles g ms last)[i]
    let hθ:∀i:Fin (cofiniteConstructionAngles g ms last).length,θ i∈Ico (0:ℝ) Real.pi:=
      fun i=>cofiniteConstruction_angles_mem g ms last (fun m hm=>Or.inr (hms m hm))
        (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
    let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
      (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
    let ρ:=cofiniteConstructionPairing g ms last
    let hρ:=cofiniteConstructionPairing_involutive g ms last
    let hθρ:=cofiniteConstructionPairing_angle_profile g ms last
    let hPeriod:∀i:Fin (cofiniteConstructionAngles g ms last).length,
        ∃N:ℕ,3≤N ∧((ρ.trans (finRotate _))^[N]) i=i ∧θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N:=
      cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef
    let hD:=cofiniteTangential_projective_disc_convex θ d hθ hd hb hf ρ hρ hθρ hPeriod
    Nat.card (OriginalRefinedSide hD)=4*g+2*ms.length := by
  intro θ hθ hf ρ hρ hθρ hPeriod hD
  change Nat.card (OriginalRefinedSide
    (cofiniteTangential_projective_disc_convex θ d hθ hd hb hf ρ hρ hθρ hPeriod))=_
  rw [cofiniteTangential_original_refined_side_card θ d hθ hd hb hf ρ hρ hθρ hPeriod]
  change (cofiniteConstructionAngles g ms last).length+
    Nat.card {i:Fin (cofiniteConstructionAngles g ms last).length //
      cofiniteConstructionPairing g ms last i=i}=_
  rw [cofiniteConstructionSelfSideLabelEquiv_card,cofiniteConstruction_order_two_occurrence_card]
  exact cofiniteConstruction_refined_count g ms last

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open MeasureTheory

section ActualFiniteFirstKind
variable (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>
      (cofiniteConstructionAngles g ms last)[i]) d=Real.pi)

/-- Finitely many compact closed tiles cannot cover the actual noncompact half-plane. -/
theorem cofiniteConstruction_generated_infinite :
    Infinite (cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated := by
  classical
  by_contra hn
  let S:=cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb
  let :Finite S.Generated:=not_infinite_iff_finite.mp hn
  let :Fintype S.Generated:=Fintype.ofFinite _
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  have hFD:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ volume P.interior:=
    (cofiniteConstruction_finite_poincare g ms last hms hlast hdef d hd hb).2
  have hcover:(⋃a:S.Generated,a.val '' P.carrier)=univ:=by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a,y,hy,haxy⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.closure_covering S.Generated ℍ hFD x
    exact mem_iUnion.mpr ⟨a,y,(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf).symm ▸ hy,haxy⟩
  have hcompact:IsCompact (univ:Set ℍ):=by
    rw [←hcover]
    exact isCompact_iUnion (fun a:S.Generated=>(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf).image a.val.continuous)
  exact noncompact_univ ℍ hcompact

/-- Every original actual vertex has a genuinely nontrivial whole stabilizer. -/
theorem cofiniteConstruction_vertex_stabilizer_two_le
    (i:Fin (cofiniteConstructionAngles g ms last).length) :
    2≤Nat.card (MulAction.stabilizer
      (cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated
      (cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb i)) := by
  obtain ⟨c,rfl⟩:=(cofiniteConstructionCornerLabelEquiv g ms last
    (cofiniteConstruction_base_count g ms last hdef)).surjective i
  cases c with
  | inl a=>
    rw [cofiniteConstructionCornerLabelEquiv_base,cofiniteConstruction_base_stabilizer_card]
    exact hlast
  | inr a=>
    rw [cofiniteConstructionCornerLabelEquiv_outer,cofiniteConstruction_outer_stabilizer_card]
    exact hms _ (List.getElem_mem a.val.isLt)

/-- The actual whole projective group contains a loxodromic element: all
other nonidentity types would force a finite common-interior-point group. -/
theorem cofiniteConstruction_loxodromic_exists :
    ∃f∈cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic f := by
  let H:=cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb
  let P:=cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let E:(cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated≃*H:=cofiniteTangentialGroupEquiv θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
  let :Infinite (cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb).Generated:=
    cofiniteConstruction_generated_infinite g ms last hms hlast hdef d hd hb
  let :Infinite H:=Infinite.of_injective E E.injective
  by_contra hn
  have hall:∀f∈H,f≠1→_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f:=by
    intro f hfH hf1
    rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy f hf1 with hp|hl|he
    · have hconj:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*f*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹):=
        (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius,rfl⟩)).mp hp
      exact False.elim (cofiniteConstruction_no_parabolic g ms last hms hlast hdef d hd hb
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H ⟨f,hfH⟩) hconj)
    · exact False.elim (hn ⟨f,hfH,hl⟩)
    · exact he
  obtain ⟨p,hp⟩:=(_root_.LowDimensionalTopology.Geometry.Mobius.all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint H).mp hall
  have hfin:Finite H:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed H P.asFuchsianDisc.discrete p hp
  exact not_finite H

end ActualFiniteFirstKind
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- A genuine nonstraight finite corner prevents all original vertices from
lying on one native geodesic. The original side labels are unchanged. -/
theorem finitePolygon_vertices_not_in_line_of_angle_ne_pi {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hf : ∀ i, ‖(Q.vertices i : ℂ)‖ < 1) (i : Fin n)
    (ha : Q.angle i ≠ Real.pi) (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    ¬ ∀ j, _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf j ∈ L.carrier := by
  intro hL
  have hsupport (j : Fin n) : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q j = L := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_points (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q j) L
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf).ne (Q.next_ne_self j).symm)
    · exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q j
        ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_side_iff Q hf j j).mpr (Or.inr rfl))
    · apply _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q j
      apply (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_side_iff Q hf (finRotate n j) j).mpr
      exact Or.inl ((finRotate n).symm_apply_apply j).symm
    · exact hL j
    · exact hL (finRotate n j)
  exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_rays_proper Q hf i ha
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay_support Q hf i).trans
      ((hsupport ((finRotate n).symm i)).trans
        ((hsupport i).symm.trans (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay_support Q hf i).symm)))

/-- The actual finite common-incircle polygon cannot have all of its physical
native vertices on a single geodesic. Finiteness is the original corner condition. -/
theorem cofiniteTangential_finite_vertices_not_in_line {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi)
    (hf : ∀ i, ‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i : ℂ)‖ < 1)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    ¬ ∀ i, _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) hf i ∈ L.carrier := by
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let i : Fin n := ⟨0, by have := Q.three_le; omega⟩
  apply finitePolygon_vertices_not_in_line_of_angle_ne_pi Q hf i
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]
  exact ne_of_lt (hθ i).2

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon

/-- An actual elliptic real Mobius map preserving the unordered ideal pair
zero and infinity has every native fixed center on the imaginary geodesic. -/
theorem realSL_pair_preserving_elliptic_center_re_zero
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hPair : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val '' ({((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ∞} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      {((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ∞}) (x : ℍ) (hx : A • x = x) : x.re = 0 := by
  have ht := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA
  have hc : A 1 0 ≠ 0 := by
    intro hc
    have hdet := A.det_coe
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    rw [Matrix.trace_fin_two] at ht
    nlinarith [sq_nonneg (A 0 0 - A 1 1)]
  have hInfMem : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞ ∈
      ({((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ∞} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rw [← hPair]
    exact ⟨∞, by simp, rfl⟩
  have hInf : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞ = ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hInfMem
    exact hInfMem.resolve_right (fun h => hc ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp h))
  have hZeroMem : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈
      ({((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ∞} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rw [← hPair]
    exact ⟨((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), by simp, rfl⟩
  have hZero : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ∞ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZeroMem
    exact hZeroMem.resolve_left (fun h => OnePoint.coe_ne_infty (0 : ℂ)
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val.injective (h.trans hInf.symm)))
  have ha : A 0 0 = 0 := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius, MonoidHom.comp_apply, _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
      _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_infty] at hInf
    change (if (A 1 0 : ℂ) = 0 then ∞ else
      (((A 0 0 : ℂ) / (A 1 0 : ℂ)) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hInf
    rw [ite_eq_right (Complex.ofReal_ne_zero.mpr hc)] at hInf
    exact Complex.ofReal_injective ((div_eq_zero_iff.mp (OnePoint.coe_injective hInf)).resolve_right
      (Complex.ofReal_ne_zero.mpr hc))
  have hd : A 1 1 = 0 := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius, MonoidHom.comp_apply, _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
      _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe] at hZero
    change (if (A 1 0 : ℂ) * 0 + (A 1 1 : ℂ) = 0 then ∞ else
      ((((A 0 0 : ℂ) * 0 + (A 0 1 : ℂ)) /
        ((A 1 0 : ℂ) * 0 + (A 1 1 : ℂ))) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = ∞ at hZero
    simp only [mul_zero, zero_add] at hZero
    by_contra hd
    rw [ite_eq_right (Complex.ofReal_ne_zero.mpr hd)] at hZero
    exact OnePoint.coe_ne_infty _ hZero
  have ht0 : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    rw [Matrix.trace_fin_two, ha, hd, add_zero]
  rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_zero_fixed_iff A ht0 x).mp hx]
  change A 0 0 / A 1 0 = 0
  rw [ha, zero_div]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- In an elementary discrete half-plane group containing a loxodromic,
all its actual elliptic centers lie on one genuine native geodesic. -/
theorem elementary_halfPlane_elliptic_centers_line {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H)
    (f:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfH:f∈H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic f) :
    ∃L:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,∀a∈H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic a→∀x:ℍ,
      a.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint x)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint x→x∈L.carrier := by
  obtain ⟨a,b,hab,hfa,hfb,hpair⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_loxodromic_fixed_pair H
    P.asFuchsianDisc.discrete hE f hfH hf
  have hHyp:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f:=⟨hf,_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet,_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc,P.preserves ⟨f,hfH⟩⟩
  have ha:a∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary:=by
    rw [←nielsen_openHalfPlane_frontier]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier f hHyp _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc
      (P.preserves ⟨f,hfH⟩) hfa
  have hb:b∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary:=by
    rw [←nielsen_openHalfPlane_frontier]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier f hHyp _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc
      (P.preserves ⟨f,hfH⟩) hfb
  obtain ⟨q,hqa,hqb⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_boundary_pair_normalizer a b ha hb hab
  have hnorm:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_subgroupConjugate_le_zeroInftyPairStabilizer H a b hpair
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) hqa hqb
  let L:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q⁻¹)
  refine ⟨L,?_⟩
  intro g hg hEll x hfix
  obtain ⟨B,hB⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩)
  let C:=q*B*q⁻¹
  have hCeq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*g*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹:=by
    simp only [C,map_mul,map_inv,hB]
  have hCEll:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):=by
    rw [hCeq]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hEll
  have hCPair:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C).val ''
      ({((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞}:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)={((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞}:=by
    apply hnorm
    rw [hCeq]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _ _).mpr ⟨g,hg,rfl⟩
  have hBx:B•x=x:=by
    apply UpperHalfPlane.coe_injective
    apply OnePoint.coe_injective
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hB]
    exact hfix
  have hCx:C•(q•x)=q•x:=by
    dsimp only [C]
    rw [mul_smul,mul_smul,inv_smul_smul,hBx]
  have hre:=realSL_pair_preserving_elliptic_center_re_zero C hCEll hCPair (q•x) hCx
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
  refine ⟨q•x,?_,?_⟩
  · exact hre
  · change q⁻¹•(q•x)=x
    exact inv_smul_smul q x

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open MeasureTheory
local instance cofiniteRealizationSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance cofiniteRealizationSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

section ActualFiniteNonElementary
variable (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms last).length=>
      (cofiniteConstructionAngles g ms last)[i]) d=Real.pi)

/-- The actual constructed whole group is non-elementary. Every original
vertex is a genuine elliptic center, and these cannot all lie on one geodesic. -/
theorem cofiniteConstruction_finite_nonElementary :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb) := by
  let H:=cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb
  let P:=cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb
  let originalNativeAction:=P.nativeAction
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let S:=cofiniteConstructionFinitePairing g ms last hms hlast hdef d hd hb
  let E:S.Generated≃*H:=cofiniteTangentialGroupEquiv θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
    (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
  obtain ⟨f,hfH,hfL⟩:=cofiniteConstruction_loxodromic_exists g ms last hms hlast hdef d hd hb
  intro hE
  obtain ⟨L,hL⟩:=elementary_halfPlane_elliptic_centers_line P hE f hfH hfL
  apply cofiniteTangential_finite_vertices_not_in_line θ d hθ hd hb hf L
  intro i
  let x:=cofiniteConstructionFiniteVertex g ms last hms hlast hdef d hd hb i
  have hcard:2≤Nat.card (MulAction.stabilizer S.Generated x):=
    cofiniteConstruction_vertex_stabilizer_two_le g ms last hms hlast hdef d hd hb i
  let :Finite (MulAction.stabilizer S.Generated x):=Nat.finite_of_card_ne_zero (by omega)
  let :Nontrivial (MulAction.stabilizer S.Generated x):=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,ha⟩:=exists_ne (1:MulAction.stabilizer S.Generated x)
  let b:H:=E a.val
  have hbn:b.val≠1:=by
    intro he
    apply ha
    apply Subtype.ext
    apply E.injective
    exact (Subtype.ext he).trans E.map_one.symm
  have hbfix:b•x=x:=
    (cofiniteTangentialGroupEquiv_action θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
      (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
      (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef) a.val x).trans a.property
  have hfix:b.val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint x)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint x:=by
    rw [P.nativeAction_boundary,hbfix]
  have hEll:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic b.val:=fuchsianDisc_nonidentity_fixed_elliptic P.asFuchsianDisc
    b.val b.property hbn _ (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_mem x) hfix
  exact hL b.val b.property hEll x hfix

/-- The prescribed actual finite signature is realized by a genuine group
of the first kind, rather than by an added limit-set hypothesis. -/
theorem cofiniteConstruction_finite_firstKind :
    (cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData.asFuchsianDisc.IsFirstKind := by
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let P:=(cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData
  let D:=cofiniteConstructionFiniteDiscDomain g ms last hms hlast hdef d hd hb
  have hFD:IsFuchsianFundamentalDomain P D:=
    cofiniteTangential_projective_disc_fundamental θ d hθ hd hb hf (cofiniteConstructionPairing g ms last)
      (cofiniteConstructionPairing_involutive g ms last) (cofiniteConstructionPairing_angle_profile g ms last)
      (cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef)
  have hGeo:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb))
      (fuchsianGeometricDomain P.asFuchsianDisc).carrier (geometricModelArea P.asFuchsianDisc) D:=by
    rw [geometricModelArea_asUnitDisc]
    exact hFD
  apply fuchsian_finite_area_firstKind P.asFuchsianDisc
    ((cofiniteConstruction_finite_nonElementary g ms last hms hlast hdef d hd hb).conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) hGeo
  rw [geometricModelArea_asUnitDisc]
  change P.area D≠⊤
  rw [cofiniteConstruction_physical_area]
  exact ENNReal.ofReal_ne_top

end ActualFiniteNonElementary
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- For each admissible finite-cone signature, an actual original group and
fundamental polygon attain the nonempty-mark lower side bound. The count uses
the genuine source subdivision at original self-paired half-turn centers.
This does not assert a polygon construction for an arbitrarily fixed group. -/
theorem cofiniteConstruction_finite_lower_side_bound_attained
    (g:ℕ) (ms:List ℕ) (last:ℕ) (hms:∀m∈ms,2≤m) (hlast:2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) :
    ∃H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃P:UnitDiscFuchsianGroup H,
      H.FG ∧ P.asFuchsianDisc.IsFirstKind ∧
      HasCofiniteFuchsianSignature P.asFuchsianDisc g (ms++[last]) 0 ∧
      ∃D:Set P.domain.carrier,∃hD:IsConvexFuchsianPolygon P D,
        Nat.card (OriginalRefinedSide hD)=4*g+2*(ms++[last]).length-2 := by
  obtain ⟨d,hd,hb⟩:=cofiniteConstruction_radius_exists g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef
  let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
  let hθ:∀i,θ i∈Set.Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
    (fun m hm=>Or.inr (hms m hm)) (Or.inr hlast) hdef _ (List.getElem_mem i.isLt)
  let hf:=cofiniteTangential_finite_of_positive_angles θ d hθ hd hb
    (cofiniteConstruction_angles_pos_finite g ms last hms hlast hdef)
  let ρ:=cofiniteConstructionPairing g ms last
  let hρ:=cofiniteConstructionPairing_involutive g ms last
  let hθρ:=cofiniteConstructionPairing_angle_profile g ms last
  let hPeriod:=cofiniteConstruction_finite_angular_periods g ms last hms hlast hdef
  let H:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteConstructionFiniteMobiusGroup g ms last hms hlast hdef d hd hb)
  let P:=(cofiniteConstructionFiniteHalfPlaneData g ms last hms hlast hdef d hd hb).cayleyData
  let D:=cofiniteConstructionFiniteDiscDomain g ms last hms hlast hdef d hd hb
  have hD:IsConvexFuchsianPolygon P D:=
    cofiniteTangential_projective_disc_convex θ d hθ hd hb hf ρ hρ hθρ hPeriod
  have hSig:=cofiniteConstruction_finite_actual_signature g ms last hms hlast hdef d hd hb
  refine ⟨H,P,hSig.finitelyGenerated,cofiniteConstruction_finite_firstKind g ms last hms hlast hdef d hd hb,hSig,D,hD,?_⟩
  have hcount:=cofiniteConstruction_actual_refined_side_count g ms last hms hlast hdef d hd hb
  change Nat.card (OriginalRefinedSide hD)=_ at hcount
  rw [hcount]
  simp only [List.length_append,List.length_cons,List.length_nil,zero_add]
  omega

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set

/-- Choosing one last finite mark retains the exact prescribed numerical
signature deficit, including each original repeated finite order. -/
theorem cofiniteConstruction_finite_orders_deficit (g : ℕ) (ms : List ℕ) (last : ℕ) :
    cofiniteConstructionDeficit g ms last = 2 * (g : ℝ) - 2 +
      ((ms ++ [last]).map (fun m : ℕ => (1 : ℝ) - 1 / (m : ℝ))).sum := by
  have hsum (ls : List ℕ) :
      (ls.map (fun m : ℕ => (1 : ℝ) - 1 / (m : ℝ))).sum =
        (ls.length : ℝ) - (ls.map (fun m : ℕ => (1 : ℝ) / (m : ℝ))).sum := by
    induction ls with
    | nil => simp
    | cons m ls ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [ih]
      ring
  simp only [cofiniteConstructionDeficit, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hsum]
  push_cast
  ring

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set

/-- Each admissible nonempty finite-order signature has an actual group
and original convex fundamental polygon attaining the lower side bound. -/
theorem cofiniteConstruction_nonempty_finite_lower_side_bound_attained
    (g : ℕ) (orders : List ℕ) (hne : orders ≠ []) (horders : ∀ m ∈ orders, 2 ≤ m)
    (hdef : 0 < 2 * (g : ℝ) - 2 +
      (orders.map (fun m : ℕ => (1 : ℝ) - 1 / (m : ℝ))).sum) :
    ∃ H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∃ P : UnitDiscFuchsianGroup H,
      H.FG ∧ P.asFuchsianDisc.IsFirstKind ∧
      HasCofiniteFuchsianSignature P.asFuchsianDisc g orders 0 ∧
      ∃ D : Set P.domain.carrier, ∃ hD : IsConvexFuchsianPolygon P D,
        Nat.card (OriginalRefinedSide hD) = 4 * g + 2 * orders.length - 2 := by
  obtain ⟨ms, last, hsplit⟩ := (List.eq_nil_or_concat' orders).resolve_left hne
  subst orders
  have hms : ∀ m ∈ ms, 2 ≤ m := fun m hm => horders m (List.mem_append_left [last] hm)
  have hlast : 2 ≤ last := horders last (by simp)
  have hdef' : 0 < cofiniteConstructionDeficit g ms last := by
    rw [cofiniteConstruction_finite_orders_deficit]
    exact hdef
  exact cofiniteConstruction_finite_lower_side_bound_attained g ms last hms hlast hdef'

end LowDimensionalTopology.Geometry.Fuchsian

open Set InnerProductGeometry Filter Topology
open scoped Complex.UnitDisc UpperHalfPlane Pointwise MatrixGroups ComplexConjugate NNReal OnePoint

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- A positive corner remains finite even when other original corners are ideal. -/
theorem cofiniteTangential_positive_vertex_finite {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (i:Fin n) (hi:0<θ i) :
    ‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖<1 := by
  by_contra hn
  have he:‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖=1:=
    le_antisymm ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i).norm_le_one (le_of_not_gt hn)
  have ha:θ i=0:=by
    rw [←_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle θ d hθ hd hb i,_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.angle_of_ideal _ i he]
  exact (ne_of_gt hi) ha


/-- The actual positive frames at all finite corners are constructed simultaneously.
Ideal corners are outside the finite-corner clauses, rather than assumed absent. -/
theorem cofiniteTangential_mixed_finite_frames {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    ∃(z:Fin n→𝔻)(F:Fin n→Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀i,0<θ i→Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (z i)) ∧
      (∀i,0<θ i→F i • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z i)=UpperHalfPlane.I) ∧
      (∀i,0<θ i→∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z i)),
        y∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier ↔
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • y):ℂ)∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (θ i):ℂ)}) ∧
      ∀i:Fin n,0<θ i→∀y:ℍ,
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F (finRotate n (ρ i)) • cofiniteTangentPairingElement θ d hθ hd hb i (ρ i) y):ℂ)=
          (Circle.exp (θ i):ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • y):ℂ) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  have hEx:∀i:Fin n,∃z:𝔻,∃s:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      0<θ i→∃hz:Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z,s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z=UpperHalfPlane.I ∧
      (∀y:ℍ,y∈(Q.cornerRayNext i z hz).toHalfPlane.val→y≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z→
        ∃r:ℝ,0<r ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)=(r:ℂ)) ∧
      (∀y:ℍ,y∈(Q.cornerRayPrev i z hz).toHalfPlane.val→y≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z→
        ∃r:ℝ,0<r ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)=(r:ℂ)*(Circle.exp (θ i):ℂ)) ∧
      ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z),y∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier ↔
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • y):ℂ)∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (θ i):ℂ)} := by
    intro i
    by_cases hi:0<θ i
    · let z:𝔻:=Complex.UnitDisc.mk (Q.vertices i:ℂ)
        (cofiniteTangential_positive_vertex_finite θ d hθ hd hb i hi)
      have hz:Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z:=Subtype.ext rfl
      obtain ⟨s,hs,ho,hp,hg⟩:=cofiniteTangential_polygon_frame_exists θ d hθ hd hb i z hz
      exact ⟨z,s,fun _=>⟨hz,hs,ho,hp,hg⟩⟩
    · exact ⟨0,1,fun h=>(hi h).elim⟩
  choose z F hF using hEx
  refine ⟨z,F,fun i hi=>(hF i hi).1,fun i hi=>(hF i hi).2.1,
    fun i hi=>(hF i hi).2.2.2.2,?_⟩
  intro i hi y
  let j:=ρ i
  let k:=finRotate n j
  have hk:0<θ k:=by simpa only [k,j,←hθρ i] using hi
  have hzi:Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (z i):=(hF i hi).1
  have hzk:Q.vertices k=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (z k):=(hF k hk).1
  let e:=cofiniteTangentPairingClosedIsometry θ d hθ hd hb i j
  let w:=e.finiteMap (z i)
  have hw:Q.vertices k=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w:=by
    rw [←e.finite_commutes,←hzi]
    exact (cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i j (hθρ i)).symm
  have hwz:w=z k:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective (hw.symm.trans hzk)
  have hrot:=cofiniteTangentPairing_frame_rotation θ d hθ hd hb i j (hθρ i)
    (cofiniteTangentialPairing_other_angle θ ρ hρ hθρ i) (z i) hzi
  dsimp only at hrot
  have hR:=hrot (F i) (F k) (hF i hi).2.1 (by
    change F k • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w=UpperHalfPlane.I
    rw [hwz]
    exact (hF k hk).2.1) (hF i hi).2.2.1 (by
      intro x hx hxp
      change x∈(Q.cornerRayPrev k w hw).toHalfPlane.val at hx
      have hMove:∀(v:𝔻)(hv:Q.vertices k=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel v),v=z k→
          (Q.cornerRayPrev k v hv).toHalfPlane.val=(Q.cornerRayPrev k (z k) hzk).toHalfPlane.val:=by
        intro v hv he
        subst v
        rfl
      rw [hMove w hw hwz] at hx
      have hxp':x≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z k):=by
        change x≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w at hxp
        rwa [hwz] at hxp
      obtain ⟨r,hr,he⟩:=(hF k hk).2.2.2.1 x hx hxp'
      refine ⟨r,hr,?_⟩
      rw [←hθρ i] at he
      exact he) (F i • y)
  rw [inv_smul_smul] at hR
  have h:=congrArg (fun q:𝔻=>(q:ℂ)) hR
  rw [circleDiscRotationHom_apply] at h
  exact h

end LowDimensionalTopology.Geometry.Fuchsian


namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
attribute [local instance] closedAngleFanDiscMetric
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The complete actual angular label period gives identity for the literal
native inverse-side word. The frame system is constructed internally from
the true polygon; no holonomy relation or developing-map hypothesis is added. -/
theorem cofiniteTangential_mixed_word_period {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (ρ:Equiv.Perm (Fin n))
    (hρ:Function.Involutive ρ) (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (i:Fin n) (N:ℕ) (hN:0<N)
    (hCycle:((ρ.trans (finRotate n))^[N]) i=i)
    (hAngle:θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) :
    nativeAngularWalkWord (fun j=>cofiniteTangentPairingElement θ d hθ hd hb
      (((ρ.trans (finRotate n))^[j]) i) (ρ (((ρ.trans (finRotate n))^[j]) i))) N=1 := by
  let τ:=ρ.trans (finRotate n)
  have hi:0<θ i:=by
    rw [hAngle]
    exact div_pos (by positivity) (by exact_mod_cast hN)
  obtain ⟨_z,F,_hz,_hcenter,_hgerm,hFrame⟩:=cofiniteTangential_mixed_finite_frames θ d hθ hd hb ρ hρ hθρ
  let A:ℕ→(ℍ≃ᵢℍ):=fun j=>cofiniteTangentPairingElement θ d hθ hd hb (τ^[j] i) (ρ (τ^[j] i))
  let G:ℕ→Matrix.SpecialLinearGroup (Fin 2) ℝ:=fun j=>F (τ^[j] i)
  let β:ℕ→ℝ:=fun j=>θ (τ^[j] i)
  have hStep:∀j:ℕ,∀x:ℍ,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G (j+1) • A j x):ℂ)=
      (Circle.exp (β j):ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G j • x):ℂ):=by
    intro j x
    have hj:0<θ (τ^[j] i):=by
      rw [cofiniteTangential_angle_iterate θ ρ hθρ i j]
      exact hi
    simpa only [G,A,β,Function.iterate_succ_apply',τ,Equiv.trans_apply] using
      hFrame (τ^[j] i) hj x
  have hGF:G N=G 0:=by
    dsimp only [G]
    rw [hCycle]
    rfl
  have hsum:(∑k∈Finset.range N,β k)=2*Real.pi:=by
    calc
      (∑k∈Finset.range N,β k)=∑_k∈Finset.range N,θ i:=by
        apply Finset.sum_congr rfl
        intro k _hk
        exact cofiniteTangential_angle_iterate θ ρ hθρ i k
      _=(N:ℝ)*θ i:=by simp
      _=2*Real.pi:=by rw [hAngle];exact _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod_mul N hN.ne'
  have hTurn:Circle.exp (∑k∈Finset.range N,β k)=1:=by
    rw [hsum,Circle.exp_two_pi]
  exact nativeAngularWalk_word_eq_one A G β hStep N hGF hTurn

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
attribute [local instance] tangentialFanDiscMetric
/-- The literal inverse-side word tiles a genuine ball at the original finite
corner, using the actual internally constructed positive frames. -/
theorem cofiniteTangential_mixed_cycle_ball_fan {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (ρ:Equiv.Perm (Fin n))
    (hρ:Function.Involutive ρ) (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (i:Fin n) (w:𝔻)
    (hw:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w)
    (N:ℕ) (hN:3≤N) (hAngle:θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) :
    let τ:=ρ.trans (finRotate n)
    let A:ℕ→(ℍ≃ᵢℍ):=fun j=>cofiniteTangentPairingElement θ d hθ hd hb (τ^[j] i) (ρ (τ^[j] i))
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)
    ∃r:ℝ,0<r ∧∀s:ℝ,0<s→s≤r→
      (⋃j:Fin N,(nativeAngularWalkWord A j.val '' P.carrier)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) s)=
        Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) s ∧
      Pairwise (fun j k:Fin N=>Disjoint
        ((nativeAngularWalkWord A j.val '' P.interior)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) s)
        ((nativeAngularWalkWord A k.val '' P.interior)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) s)) := by
  let τ:=ρ.trans (finRotate n)
  let A:ℕ→(ℍ≃ᵢℍ):=fun j=>cofiniteTangentPairingElement θ d hθ hd hb (τ^[j] i) (ρ (τ^[j] i))
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)
  have hi:0<θ i:=by
    rw [hAngle]
    exact div_pos (by positivity) (by exact_mod_cast (by omega:0<N))
  have hPos (j:ℕ):0<θ (τ^[j] i):=by
    rw [cofiniteTangential_angle_iterate θ ρ hθρ i j]
    exact hi
  obtain ⟨z,F,hz,hcenter,hgerm,hFrame⟩:=cofiniteTangential_mixed_finite_frames θ d hθ hd hb ρ hρ hθρ
  have hzi:z i=w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective ((hz i hi).symm.trans hw)
  let G:ℕ→Matrix.SpecialLinearGroup (Fin 2) ℝ:=fun j=>F (τ^[j] i)
  let β:ℕ→ℝ:=fun j=>θ (τ^[j] i)
  have hStep:∀j:ℕ,∀x:ℍ,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G (j+1) • A j x):ℂ)=
      (Circle.exp (β j):ℂ)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G j • x):ℂ):=by
    intro j x
    simpa only [G,A,β,Function.iterate_succ_apply',τ,Equiv.trans_apply] using
      hFrame (τ^[j] i) (hPos j) x
  let u:Circle:=(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator N)⁻¹
  have hu:orderOf u=N:=by
    change orderOf ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator N)⁻¹)=N
    rw [orderOf_inv]
    exact (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot N (by omega)).eq_orderOf.symm
  have hphase (j:ℕ):Circle.exp (-(∑k∈Finset.range j,β k))=u^j:=by
    have hsum:(∑k∈Finset.range j,β k)=(j:ℝ)*θ i:=by
      calc
        _=∑_k∈Finset.range j,θ i:=by
          apply Finset.sum_congr rfl
          intro k _hk
          exact cofiniteTangential_angle_iterate θ ρ hθρ i k
        _=_:=by simp
    rw [hsum,hAngle,neg_mul_eq_mul_neg,Circle.exp_natCast_mul,Circle.exp_neg]
    rfl
  have hcoord (j:ℕ) (x:ℍ):
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • nativeAngularWalkWord A j x)=
        circleDiscRotationHom (u^j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G j • x)):=by
    apply Complex.UnitDisc.coe_injective
    have hh:=nativeAngularWalk_coordinate A G β hStep j x
    simpa only [G,Function.iterate_zero,Function.id_def,hphase,circleDiscRotationHom_apply] using hh
  have hWordCenter (j:ℕ):nativeAngularWalkWord A j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j] i)))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w:=by
    apply (isometry_smul ℍ (F i)).injective
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • nativeAngularWalkWord A j (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j] i))))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (F i • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)
    rw [hcoord]
    dsimp only [G]
    rw [hcenter (τ^[j] i) (hPos j)]
    have hci:F i • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w=UpperHalfPlane.I:=by simpa only [hzi] using hcenter i hi
    rw [hci]
    have h0:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=0:=by
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    rw [h0]
    apply Complex.UnitDisc.coe_injective
    change ((u^j:Circle):ℂ)*(0:ℂ)=0
    exact mul_zero _
  let e:ℍ≃ᵢ𝔻:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F i)).trans triangleVertexCayleyIsometry
  let C:Fin N→Set ℍ:=fun j=>nativeAngularWalkWord A j.val '' P.carrier
  let O:Fin N→Set ℍ:=fun j=>nativeAngularWalkWord A j.val '' P.interior
  have hGerm:∀j:Fin N,∀ᶠx in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w),
      x∈C j ↔e x∈circleDiscRotationHom (u^j.val) ''
        {q:𝔻|(q:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector N}:=by
    intro j
    have hcont:Continuous (((nativeAngularWalkWord A j.val).symm):ℍ→ℍ):=
      ((nativeAngularWalkWord A j.val).symm).continuous
    have hpre:((nativeAngularWalkWord A j.val).symm) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j.val] i)):=by
      rw [←hWordCenter j.val]
      exact (nativeAngularWalkWord A j.val).symm_apply_apply _
    have ht:Tendsto (((nativeAngularWalkWord A j.val).symm):ℍ→ℍ)
        (𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)) (𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j.val] i)))):=by
      simpa only [hpre] using hcont.tendsto (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w)
    filter_upwards [ht.eventually (hgerm (τ^[j.val] i) (hPos j.val))] with x hx
    have hin:x∈C j ↔((nativeAngularWalkWord A j.val).symm x)∈P.carrier:=by
      constructor
      · rintro ⟨y,hy,rfl⟩
        simpa only [(nativeAngularWalkWord A j.val).symm_apply_apply] using hy
      · intro hy
        exact ⟨_,hy,(nativeAngularWalkWord A j.val).apply_symm_apply x⟩
    rw [hin,hx,cofiniteTangential_angle_iterate θ ρ hθρ i j.val,hAngle]
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G j.val • (nativeAngularWalkWord A j.val).symm x):ℂ)∈
      (Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N):ℂ)}:Set ℂ)) ↔_
    rw [←_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector_eq_span N hN]
    have he:e x=circleDiscRotationHom (u^j.val)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (G j.val • ((nativeAngularWalkWord A j.val).symm x))):=by
      have hh:=hcoord j.val (((nativeAngularWalkWord A j.val).symm) x)
      rw [(nativeAngularWalkWord A j.val).apply_symm_apply] at hh
      exact hh
    rw [he]
    constructor
    · intro hy
      exact mem_image_of_mem (circleDiscRotationHom (u^j.val)) hy
    · rintro ⟨q,hq,hqeq⟩
      exact (circleDiscRotationHom (u^j.val)).injective hqeq ▸ hq
  have hOpen:∀j,IsOpen (O j):=by
    intro j
    exact (nativeAngularWalkWord A j.val).toHomeomorph.isOpenMap _ (by exact _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_interior_isOpen _)
  have hOC:∀j,O j⊆C j:=by
    intro j
    exact Set.image_mono P.interior_subset_carrier
  exact native_closed_angle_germs_ball_fan N (by omega) u hu (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) e C O hGerm hOpen hOC

end LowDimensionalTopology.Geometry.Fuchsian


namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A singleton ideal natural cycle has a nonidentity genuine parabolic
monodromy, proved from its actual two reflection factors. -/
theorem cofiniteTangentPairingElement_ideal_singleton_parabolic {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hstep:finRotate n j=i) (hzero:θ i=0) :
    ∃f:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀z:ℍ,f • z=cofiniteTangentPairingElement θ d hθ hd hb i j z) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius f) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let N:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i
  let q:=Q.vertices i
  have hq:‖(q:ℂ)‖=1:=cofiniteTangential_zero_vertex_ideal θ d hθ hd i hzero
  obtain ⟨L,hM,hLI,hClosed⟩:=cofiniteTangentMirror_genuine_line θ d i j
  have hNe:N≠L:=by
    intro he
    apply cofiniteTangential_side_avoids_origin θ d hθ hd hb i
    change UpperHalfPlane.I∈N.carrier
    rw [he]
    exact hLI
  have hqMirror:cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j) q=q:=by
    have hh:=cofiniteTangentMirror_vertex_left θ d hθ hd hb i j (by rw [hstep])
    change cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i
    simpa only [hstep] using hh
  have hqL:q∈L.toDiscLine.closedCarrier:=
    (L.toDiscLine.closedReflectionIsometry_fixed_iff q).mp ((hClosed q).trans hqMirror)
  have hqN:q∈N.toDiscLine.closedCarrier:=by
    change q∈(Q.geodesicSide i).toHalfPlane.toDiscLine.closedCarrier
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane_spec]
    exact (Q.geodesicSide_endpoints i).1
  have hNative (K:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (hk:q∈K.toDiscLine.closedCarrier) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended q)∈K.idealEndpoints:=by
    have he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended q∈K.toDiscLine.idealEndpoints:=
      (K.toDiscLine.closedCarrier_mem_ideal_iff q hq).mp hk
    rw [K.toDiscLine_idealEndpoints] at he
    obtain ⟨x,hx,hxe⟩:=he
    simpa only [←hxe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm_apply_apply] using hx
  let p:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended q)
  have hpN:p∈N.idealEndpoints:=hNative N hqN
  have hpL:p∈L.idealEndpoints:=hNative L hqL
  have hparallel:N.Parallel L:=by
    refine ⟨hNe,p,?_⟩
    ext x
    constructor
    · intro hx
      exact Set.mem_singleton_iff.mpr ((N.idealEndpoints_inter_subsingleton L hNe) hx ⟨hpN,hpL⟩)
    · intro hx
      have hh:=Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨hpN,hpL⟩
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L N
  have hAct (z:ℍ):f • z=cofiniteTangentPairingElement θ d hθ hd hb i j z:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L (N.reflection z)=_
    rw [hM]
    rfl
  have hf:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius f≠1:=by
    intro he
    have hI:f • UpperHalfPlane.I=UpperHalfPlane.I:=by
      have hh:=congrArg (fun F:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>F.val ((UpperHalfPlane.I:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) he
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action] at hh
      exact UpperHalfPlane.ext (OnePoint.coe_eq_coe.mp hh)
    have hNI:N.reflection UpperHalfPlane.I=UpperHalfPlane.I:=by
      apply L.reflection_isometry.injective
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action,hI,(L.reflection_fixed_iff _).mpr hLI]
    exact cofiniteTangential_side_avoids_origin θ d hθ hd hb i
      ((N.reflection_fixed_iff _).mp hNI)
  refine ⟨f,hAct,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_parallel_reflections_parabolic f hf N L hparallel ?_⟩
  funext z
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action L N z


/-- The actual singleton cusp monodromy has no native interior fixed point. -/
theorem cofiniteTangentPairingElement_ideal_singleton_no_fixed {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hstep:finRotate n j=i) (hzero:θ i=0) (z:ℍ) :
    cofiniteTangentPairingElement θ d hθ hd hb i j z≠z := by
  obtain ⟨f,hAct,hpar⟩:=cofiniteTangentPairingElement_ideal_singleton_parabolic θ d hθ hd hb i j hstep hzero
  rw [←hAct]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_parabolic_no_fixed f hpar z

/-- In particular the literal native side-pairing element is nonidentity. -/
theorem cofiniteTangentPairingElement_ideal_singleton_ne_one {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i j:Fin n)
    (hstep:finRotate n j=i) (hzero:θ i=0) :
    cofiniteTangentPairingElement θ d hθ hd hb i j≠1 := by
  intro he
  have hn:=cofiniteTangentPairingElement_ideal_singleton_no_fixed θ d hθ hd hb i j hstep hzero UpperHalfPlane.I
  apply hn
  rw [he]
  rfl

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
  Filter
  Topology
  InnerProductGeometry

theorem cofiniteJordan_carrier_iff {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (z : ℍ) :
    z∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈Q.closedCarrier := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier]
  change z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph ⁻¹' Q.interior) ↔
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel '' Q.interior)
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.preimage_closure]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈closure Q.interior ↔_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.closure_eq_preimage_closure_image Q.interior]
  rfl


theorem cofiniteJordan_carrier_support_iff {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (z : ℍ) :
    z∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier ↔
      ∀i,inner ℝ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha).normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha).offsets i := by
  let A:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha
  have hAQ : A.toDiscPolygon=Q := Q.strictSupportData_toDiscPolygon hQ ha
  have hBody : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.closedCarrier=A.kleinRegion := by
    rw [←hAQ]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.centeredPolygon_closedCarrier_klein_image A
  rw [cofiniteJordan_carrier_iff]
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈Q.closedCarrier ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))∈A.kleinRegion := by
    rw [←hBody]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.symm
  rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
  rfl


theorem cofiniteJordan_side_eq_carrier_inter_line {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier∩(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier := by
  let A:=(Q.strictSupportData hQ ha).toCenteredData
  have hAQ : A.toDiscPolygon=Q := Q.strictSupportData_toDiscPolygon hQ ha
  have hAL : A.supportLine i=Q.geodesicSide i := Q.strictSupportData_supportLine hQ ha i
  have hBody : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.closedCarrier=A.kleinRegion := by
    rw [←hAQ]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.centeredPolygon_closedCarrier_klein_image A
  have hLine (z : ℍ) : z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier ↔
      inner ℝ (A.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)))=A.offsets i := by
    rw [←A.supportLine_equation]
    rw [hAL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_mem_interior_iff,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.mem_carrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
    rfl
  ext z
  constructor
  · intro hz
    have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))∈A.kleinFace i := by
      rw [←A.edge_image_eq_face]
      exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z),hz,rfl⟩
    have hP : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈Q.closedCarrier := by
      have hh:=hK.1
      rw [←hBody] at hh
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp hh
    exact ⟨(cofiniteJordan_carrier_iff Q z).mpr hP,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hz⟩
  · rintro ⟨hP,hL⟩
    have hcP := (cofiniteJordan_carrier_iff Q z).mp hP
    have hBodyP : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))∈A.kleinRegion := by
      rw [←hBody]
      exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z),hcP,rfl⟩
    have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z))∈A.kleinFace i :=
      ⟨hBodyP,(hLine z).mp hL⟩
    rw [←A.edge_image_eq_face] at hK
    have hz := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp hK
    exact hz


theorem cofiniteJordan_other_support_strict {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi)
    {i : Fin n} {z : ℍ} (hi : z∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i)
    (hv : z∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q) {j : Fin n} (hj : j≠i) :
    inner ℝ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha).normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha).offsets j := by
  have hP : z∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier :=
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i) hi
  have hw := (cofiniteJordan_carrier_support_iff Q hQ ha z).mp hP j
  apply lt_of_le_of_ne hw
  intro he
  have hL := (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha j z).mpr he
  have hjs : z∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q j := by
    rw [cofiniteJordan_side_eq_carrier_inter_line Q hQ ha j]
    exact ⟨hP,hL⟩
  exact hv (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q hj.symm hi hjs)

/-- Near a genuine nonvertex side point, all other original support inequalities disappear;
the original closed polygon is exactly the one actual supporting closed half-plane. -/
theorem cofiniteJordan_nonvertex_support_germ {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi)
    {i : Fin n} {z : ℍ} (hi : z∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i)
    (hv : z∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q) :
    ∃r : ℝ,0<r ∧ ∀w : ℍ,dist w z<r →
      (w∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier ↔
        inner ℝ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha).normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)≤
          (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha).offsets i) := by
  let A:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha
  let U : Set ℍ:=⋂j,⋂(_ : j≠i),{w : ℍ|inner ℝ (A.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)<A.offsets j}
  have hU : IsOpen U := isOpen_iInter_of_finite (fun j=>isOpen_iInter_of_finite (fun _=>
    isOpen_lt (continuous_const.inner _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous) continuous_const))
  have hzU : z∈U := by
    apply mem_iInter.mpr
    intro j
    apply mem_iInter.mpr
    intro hj
    exact cofiniteJordan_other_support_strict Q hQ ha hi hv hj
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  refine ⟨r,hr,?_⟩
  intro w hw
  rw [cofiniteJordan_carrier_support_iff Q hQ ha w]
  constructor
  · exact fun h=>h i
  · intro h j
    by_cases hj : j=i
    · simpa only [hj] using h
    · exact (mem_iInter₂.mp (hBall hw) j hj).le


end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
  Filter
  Topology
  InnerProductGeometry

/-- The unchanged finite-or-ideal polygon has literal original endpoint data. -/
def cofiniteJordanSideIntervals {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) :
    _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicSideIntervals (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q) where
  startPoint s:=Q.vertices ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm s)
  endPoint s:=Q.vertices (finRotate n ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm s))
  endpoint_ne s:=Q.vertices_injective.ne (Q.next_ne_self _).symm
  side_eq:=by
    intro s
    obtain ⟨i,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).surjective s
    rw [(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm_apply_apply]
    rfl
  locallyFinite:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_locallyFiniteSides Q
  side_intersection:=by
    intro s t hst x hx ht
    obtain ⟨i,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).surjective s
    obtain ⟨j,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).surjective t
    have hij:i≠j:=fun he=>hst (congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q) he)
    rw [(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm_apply_apply]
    exact (Q.simple_edges i j hij ⟨hx,ht⟩).1


theorem cofiniteJordanSideIntervals_vertices {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) :
    (cofiniteJordanSideIntervals Q).vertices=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q := by
  ext x
  constructor
  · intro hx
    obtain ⟨s,hs⟩:=mem_iUnion.mp hx
    obtain ⟨i,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).surjective s
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈
      ({Q.vertices ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i)),
        Q.vertices (finRotate n ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i)))}:Set 𝕔𝔻) at hs
    rw [(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm_apply_apply] at hs
    rcases hs with hs|hs
    · exact ⟨i,hs.symm⟩
    · exact ⟨finRotate n i,hs.symm⟩
  · rintro ⟨i,hi⟩
    apply mem_iUnion.mpr
    refine ⟨_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i,?_⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈
      ({Q.vertices ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i)),
        Q.vertices (finRotate n ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i)))}:Set 𝕔𝔻)
    rw [(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm_apply_apply,hi]
    exact mem_insert _ _


/-- Any original side pairing preserves precisely the actual native vertices,
including when other original endpoints are ideal. -/
theorem cofiniteJordan_pairing_preserves_vertices {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q))
    (x:ℍ) (hx:x∈_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q)
    (s:(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).Side) (hxs:x∈s.val) :
    S.element s x∈_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q := by
  rw [←cofiniteJordanSideIntervals_vertices Q] at hx ⊢
  exact (cofiniteJordanSideIntervals Q).pairing_preserves_vertices S x hx s hxs


/-- A nondegenerate ideal side still determines its true signed Lorentz support. -/
theorem cofiniteJordan_side_signed_support {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) (i : Fin n) :
    ∃σ : ℝ,σ≠0 ∧ ∀z : ℍ,
      (0≤σ*(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).normalTimeAt z ↔
        inner ℝ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha).normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤
          (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha).offsets i) := by
  let A:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha
  have hm:A.normals i≠0:=by
    intro h
    have hn:=A.normal_norm i
    rw [h,norm_zero] at hn
    norm_num at hn
  obtain ⟨a,haS,b,hbS,hab⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeCompactifiedSide_nontrivial
    (Q.vertices i) (Q.vertices (finRotate n i))
    (Q.vertices_injective.ne (Q.next_ne_self i).symm)
  have hla:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i haS
  have hlb:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hbS
  exact _root_.LowDimensionalTopology.Geometry.Polygon.native_halfPlane_signed_support (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i) hm hab hla hlb
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha i a).mp hla)
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha i b).mp hlb)


/-- The two actual reflected closed pieces cover a true neighborhood of each
nonvertex side point, independently of finite or ideal endpoint status. -/
theorem cofiniteJordan_nonvertex_reflection_cover {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (hQ : Q.IsConvex)
    (ha : ∀i,Q.angle i<Real.pi) {i : Fin n} {x : ℍ}
    (hx:x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i) (hv:x∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q) :
    ∀ᶠz in 𝓝 x,z∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier ∨
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).reflection z∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).carrier := by
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
  let N:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i
  obtain ⟨r,hr,hG⟩:=cofiniteJordan_nonvertex_support_germ Q hQ ha hx hv
  obtain ⟨σ,_hσ,hCut⟩:=cofiniteJordan_side_signed_support Q hQ ha i
  have hfix:N.reflection x=x:=(N.reflection_fixed_iff x).mpr
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hx)
  have hdist (z:ℍ):dist (N.reflection z) x=dist z x:=by
    calc
      dist (N.reflection z) x=dist (N.reflection z) (N.reflection x):=by rw [hfix]
      _=dist z x:=N.reflection_isometry.dist_eq z x
  filter_upwards [Metric.ball_mem_nhds x hr] with z hz
  have hz':dist z x<r:=hz
  rcases le_total 0 (σ*N.normalTimeAt z) with hp|hn
  · exact Or.inl ((hG z hz').mpr ((hCut z).mp hp))
  · apply Or.inr
    apply (hG (N.reflection z) (by rwa [hdist])).mpr
    apply (hCut (N.reflection z)).mp
    rw [N.normalTimeAt_self_reflection,mul_neg]
    linarith


/-- Every true side germ is its actual inward component, with the same
physical incircle center serving as the reference point for all sides. -/
theorem cofiniteTangential_jordan_nonvertex_incircle_component_germ {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (i:Fin n) (x:ℍ) (hx:x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i)
    (hv:x∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)) :
    ∀ᶠw in 𝓝 x,
      w∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).carrier ↔
        w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i) UpperHalfPlane.I := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
  have hQ:Q.IsConvex:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb
  have ha:∀j,Q.angle j<Real.pi:=by
    intro j
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]
    exact (hθ j).2
  let B:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha
  let N:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i
  have hII:UpperHalfPlane.I∈P.interior:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I∈Q.interior
    have hz:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=0:=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero])
    rw [hz]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_origin_mem θ d hθ hd hb
  have hIle:inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate UpperHalfPlane.I)≤B.offsets i:=
    (cofiniteJordan_carrier_support_iff Q hQ ha UpperHalfPlane.I).mp
      (P.interior_subset_carrier hII) i
  have hIlt:inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate UpperHalfPlane.I)<B.offsets i:=by
    apply lt_of_le_of_ne hIle
    intro he
    exact cofiniteTangential_side_avoids_origin θ d hθ hd hb i
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha i UpperHalfPlane.I).mpr he)
  have hm:B.normals i≠0:=by
    intro he
    have hh:=B.normal_norm i
    rw [he,norm_zero] at hh
    norm_num at hh
  have hCut:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N UpperHalfPlane.I=
      {z:ℍ|inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤B.offsets i}:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlane_eq_le N (B.normals i) (B.offsets i) hm
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha i) UpperHalfPlane.I hIlt
  obtain ⟨r,hr,hG⟩:=cofiniteJordan_nonvertex_support_germ Q hQ ha hx hv
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨r,hr,?_⟩
  intro w hw
  rw [hCut]
  exact hG w hw


/-- The actual original side map at its unchanged finite-or-ideal label. -/
theorem cofiniteTangentialJordanSidePairing_element_index {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) :
    (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).element
      (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i)=
      cofiniteTangentPairingElement θ d hθ hd hb i (ρ i) := by
  change cofiniteTangentPairingElement θ d hθ hd hb
    ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _ i))
    (ρ ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _ i)))=_
  rw [(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _).symm_apply_apply]


theorem cofiniteTangentialJordanSidePairing_paired_index {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) :
    (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).paired
      (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i)=
      _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) (ρ i) := by
  change _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _
    (ρ ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _ i)))=_
  rw [(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _).symm_apply_apply]


/-- The genuine original side convention holds also on sides with ideal endpoints. -/
theorem cofiniteTangential_jordan_opposite_side_neighborhoods {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (x:ℍ)
    (hx:x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i)
    (hv:x∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)) :
    (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).OppositeSideNeighborhoods
      (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i) x := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
  let S:=cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
  let s:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i (ρ i))
  let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i)
  let :IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hr:θ (finRotate n i)=θ (ρ i):=by
    simpa only [hρ i] using (hθρ (ρ i)).symm
  have hRx:R x=x:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).reflection_fixed_iff x |>.mpr
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hx)
  have hAx:S.element s x=M x:=by
    rw [cofiniteTangentialJordanSidePairing_element_index θ d hθ hd hb ρ hρ hθρ i]
    change M (R x)=M x
    rw [hRx]
  have hy:M x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q (ρ i):=by
    rw [←cofiniteTangentMirror_native_side_image θ d hθ hd hb i (ρ i) (hθρ i) hr]
    exact mem_image_of_mem M hx
  have hyv:M x∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q:=by
    intro hyV
    have hySide:S.element s x∈(S.paired s).val:=by
      rw [←S.side_image]
      exact mem_image_of_mem (S.element s) hx
    have hh:=cofiniteJordan_pairing_preserves_vertices Q S (S.element s x)
      (hAx.symm ▸ hyV) (S.paired s) hySide
    rw [S.element_paired] at hh
    change (S.element s).symm (S.element s x)∈_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q at hh
    rw [(S.element s).symm_apply_apply] at hh
    exact hv hh
  have hi:=cofiniteTangential_jordan_nonvertex_incircle_component_germ θ d hθ hd hb i x hx hv
  have hj:=cofiniteTangential_jordan_nonvertex_incircle_component_germ θ d hθ hd hb (ρ i) (M x) hy hyv
  have hj':∀ᶠz in 𝓝 x,
      M z∈P.carrier ↔M z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q (ρ i)) UpperHalfPlane.I:=
    (M.continuous.tendsto x).eventually hj
  have hLocal:∀ᶠz in 𝓝 x,M z∈P.carrier ↔z∈P.carrier:=by
    filter_upwards [hi,hj'] with z hiz hjz
    exact hjz.trans ((cofiniteTangentMirror_native_inward_iff θ d hθ hd hb i (ρ i) (hθρ i) hr z).trans hiz.symm)
  have hRt:Tendsto R (𝓝 x) (𝓝 x):=by
    simpa only [hRx] using R.continuous.tendsto x
  have hReflect:∀ᶠz in 𝓝 x,M (R z)∈P.carrier ↔R z∈P.carrier:=hRt.eventually hLocal
  have ha:∀j,Q.angle j<Real.pi:=by
    intro j
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]
    exact (hθ j).2
  have hOld:=cofiniteJordan_nonvertex_reflection_cover Q
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb) ha hx hv
  apply (S.oppositeSideNeighborhoods_iff s x).mpr
  filter_upwards [hOld,hReflect] with z hz hRefl
  change z∈P.carrier ∨S.element s z∈P.carrier
  rcases hz with hz|hz
  · exact Or.inl hz
  · apply Or.inr
    rw [cofiniteTangentialJordanSidePairing_element_index θ d hθ hd hb ρ hρ hθρ i]
    exact hRefl.mpr hz


/-- All actual original side labels satisfy the original convention, without any
assumption that their endpoints are finite. -/
theorem cofiniteTangential_jordan_all_opposite_side_neighborhoods {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let S:=cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
    ∀s:(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).Side,∀x∈s.val,
      x∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q → S.OppositeSideNeighborhoods s x := by
  dsimp only
  intro s x hx hv
  obtain ⟨i,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _).surjective s
  exact cofiniteTangential_jordan_opposite_side_neighborhoods θ d hθ hd hb ρ hρ hθρ i x hx hv

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The original inverse-side word, retaining all finite and ideal labels. -/
def cofiniteTangentialJordanWord {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) :
    ℕ→(cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).Generated
  | 0=>1
  | j+1=>cofiniteTangentialJordanWord θ d hθ hd hb ρ hρ hθρ i j*
      ((cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).generator
        (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)
          (((ρ.trans (finRotate n))^[j]) i)))⁻¹


theorem cofiniteTangentialJordanWord_native_value {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (j:ℕ) :
    (cofiniteTangentialJordanWord θ d hθ hd hb ρ hρ hθρ i j).val=
      nativeAngularWalkWord (fun k=>cofiniteTangentPairingElement θ d hθ hd hb
        (((ρ.trans (finRotate n))^[k]) i) (ρ (((ρ.trans (finRotate n))^[k]) i))) j := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    change (cofiniteTangentialJordanWord θ d hθ hd hb ρ hρ hθρ i j).val*
      ((cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).element
        (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _ (((ρ.trans (finRotate n))^[j]) i)))⁻¹=_
    rw [ih,cofiniteTangentialJordanSidePairing_element_index]
    rfl


/-- Literal finite corner coordinates are carried to their prescribed next corners. -/
theorem cofiniteTangentialJordanPairing_vertex {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (z:Fin n→𝔻) (hz:∀i,0<θ i→(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (z i))
    (i:Fin n) (hi:0<θ i) :
    cofiniteTangentPairingElement θ d hθ hd hb i (ρ i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z i))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (finRotate n (ρ i))) := by
  exact cofiniteTangentPairingElement_vertex_eq θ d hθ hd hb i (ρ i) (hθρ i)
    (z i) (z (finRotate n (ρ i))) (hz i hi)
    (hz (finRotate n (ρ i)) (by rwa [←hθρ i]))


theorem cofiniteTangentialJordanWord_center {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (z:Fin n→𝔻) (hz:∀i,0<θ i→(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (z i))
    (i:Fin n) (hi:0<θ i) (j:ℕ) :
    (cofiniteTangentialJordanWord θ d hθ hd hb ρ hρ hθρ i j).val
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (((ρ.trans (finRotate n))^[j]) i)))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z i) := by
  let τ:=ρ.trans (finRotate n)
  induction j with
  | zero=>rfl
  | succ j ih=>
    have hj:0<θ (τ^[j] i):=by rw [cofiniteTangential_angle_iterate θ ρ hθρ i j];exact hi
    change ((cofiniteTangentialJordanWord θ d hθ hd hb ρ hρ hθρ i j).val*
      ((cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).element
        (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv _ (τ^[j] i)))⁻¹) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j+1] i)))=_
    rw [cofiniteTangentialJordanSidePairing_element_index,Function.iterate_succ_apply']
    change (cofiniteTangentialJordanWord θ d hθ hd hb ρ hρ hθρ i j).val
      ((cofiniteTangentPairingElement θ d hθ hd hb (τ^[j] i) (ρ (τ^[j] i)))⁻¹
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (finRotate n (ρ (τ^[j] i))))))=_
    rw [←cofiniteTangentialJordanPairing_vertex θ d hθ hd hb ρ hθρ z hz (τ^[j] i) hj,
      IsometryEquiv.inv_apply_self]
    exact ih


/-- A genuine finite corner has precisely its original incoming and outgoing side labels. -/
theorem cofiniteJordan_vertex_side_labels {n:ℕ} (Q:_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (i:Fin n) (z:𝔻)
    (hz:Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (s:(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).Side)
    (hs:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z∈s.val) :
    s=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q ((finRotate n).symm i) ∨s=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i := by
  obtain ⟨j,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).surjective s
  by_cases hji:j=i
  · exact Or.inr (congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q) hji)
  · have hiS:Q.vertices i∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge Q.vertices i:=_root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _
    have hjS:Q.vertices i∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge Q.vertices j:=by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge Q.vertices j at hs
      rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,←hz] at hs
    have he:=(Q.simple_edges i j (Ne.symm hji) ⟨hiS,hjS⟩).2
    rcases he with he|he
    · exact (hji (Q.vertices_injective he.symm)).elim
    · exact Or.inl (congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q)
        ((finRotate n).injective (by rw [(finRotate n).apply_symm_apply];exact (Q.vertices_injective he).symm)))


/-- Every finite angular period of the original mixed polygon gives an actual
complete natural vertex cycle; all other corners may be ideal. -/
theorem cofiniteTangential_mixed_natural_vertex_cycle {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i))) (i:Fin n) (N:ℕ) (hN:3≤N+1)
    (hCycle:((ρ.trans (finRotate n))^[N+1]) i=i) (hAngle:θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod (N+1))
    (w:𝔻) (hw:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
    let S:=cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
    ∃hx:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w∈P.carrier,∃r:ℝ,
      ∃c:S.VertexCycle {p:P.Point|p.val∈_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q} ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w,hx⟩ r,
        Nonempty (c.NaturalLabels S) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
  let S:=cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
  let E:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q
  let τ:=ρ.trans (finRotate n)
  let W:=cofiniteTangentialJordanWord θ d hθ hd hb ρ hρ hθρ i
  let A:ℕ→(ℍ≃ᵢℍ):=fun j=>cofiniteTangentPairingElement θ d hθ hd hb (τ^[j] i) (ρ (τ^[j] i))
  have hi:0<θ i:=by
    rw [hAngle]
    exact div_pos (by positivity) (by exact_mod_cast (by omega:0<N+1))
  have hPos (j:ℕ):0<θ (τ^[j] i):=by rw [cofiniteTangential_angle_iterate θ ρ hθρ i j];exact hi
  obtain ⟨z,_F,hz,_hcenter,_hgerm,_hFrame⟩:=cofiniteTangential_mixed_finite_frames θ d hθ hd hb ρ hρ hθρ
  have hzi:z i=w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective ((hz i hi).symm.trans hw)
  have hSide (j:ℕ):_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j] i))∈(E (τ^[j] i)).val:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j] i))))∈
      _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge Q.vertices (τ^[j] i)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,←hz (τ^[j] i) (hPos j)]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _
  let X:ℕ→P.Point:=fun j=>⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j] i)),P.side_subset_carrier (E (τ^[j] i)) (hSide j)⟩
  have hW:W (N+1)=1:=by
    apply Subtype.ext
    rw [cofiniteTangentialJordanWord_native_value]
    exact cofiniteTangential_mixed_word_period θ d hθ hd hb ρ hρ hθρ i (N+1) (by omega) hCycle hAngle
  have hX:X (N+1)=X 0:=by
    apply Subtype.ext
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[N+1] i))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z i)
    rw [hCycle]
  let C:Fin (N+1)→S.Copy:=fun j=>(W j.val,X j.val)
  let labels:Fin (N+1)→P.Side:=fun j=>E (τ^[j.val] i)
  have hStepPoint (j:ℕ):(X (j+1)).val=S.generator (E (τ^[j] i)) •(X j).val:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j+1] i))=S.element (E (τ^[j] i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j] i)))
    rw [cofiniteTangentialJordanSidePairing_element_index,Function.iterate_succ_apply']
    exact (cofiniteTangentialJordanPairing_vertex θ d hθ hd hb ρ hθρ z hz (τ^[j] i) (hPos j)).symm
  have hCross:∀j:Fin (N+1),∃hj:(C j).2.val∈(labels j).val,
      S.sideMateCopy (C j) (labels j) hj=C (finRotate (N+1) j):=by
    intro j
    refine Fin.lastCases ?_ (fun k=>?_) j
    · refine ⟨hSide N,?_⟩
      rw [finRotate_last]
      apply Prod.ext
      · change W N*(S.generator (E (τ^[N] i)))⁻¹=W 0
        change W (N+1)=1
        exact hW
      · apply Subtype.ext
        change S.generator (E (τ^[N] i)) •(X N).val=(X 0).val
        exact (hStepPoint N).symm.trans (congrArg Subtype.val hX)
    · refine ⟨hSide k.val,?_⟩
      have hrot:finRotate (N+1) k.castSucc=k.succ:=finRotate_of_lt k.isLt
      rw [hrot]
      apply Prod.ext
      · rfl
      · exact Subtype.ext (hStepPoint k.val).symm
  obtain ⟨r,hr,hFan⟩:=cofiniteTangential_mixed_cycle_ball_fan θ d hθ hd hb ρ hρ hθρ i w hw (N+1) hN hAngle
  obtain ⟨hCover,hDis⟩:=hFan r hr le_rfl
  have hPiece (j:Fin (N+1)) (U:Set ℍ):
      (fun x:ℍ=>(C j).1.val x) '' (U∩Metric.ball (C j).2.val r)=
        (nativeAngularWalkWord A j.val '' U)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) r:=by
    let f:ℍ≃ᵢℍ:=(W j.val).val
    change f '' (U∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j.val] i))) r)=_
    rw [Set.image_inter f.injective,f.image_ball,
      cofiniteTangentialJordanWord_center θ d hθ hd hb ρ hρ hθρ z hz i hi j.val,hzi]
    rw [show f=nativeAngularWalkWord A j.val by
      exact cofiniteTangentialJordanWord_native_value θ d hθ hd hb ρ hρ hθρ i j.val]
  have hx:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w∈P.carrier:=by
    have hh:=(X 0).property
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z i)∈P.carrier at hh
    rwa [hzi] at hh
  let c:S.VertexCycle {p:P.Point|p.val∈_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q} ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w,hx⟩ r:={
    radius_pos:=hr
    lengthPred:=N
    copies:=C
    base:=by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z i)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w
        rw [hzi]
    vertices:=by
      intro j
      refine ⟨τ^[j.val] i,?_⟩
      change Q.vertices (τ^[j.val] i)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z (τ^[j.val] i))))
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
      exact hz _ (hPos j.val)
    adjacent:=by
      intro j
      obtain ⟨hj,he⟩:=hCross j.castSucc
      have hrot:finRotate (N+1) j.castSucc=j.succ:=finRotate_of_lt j.isLt
      rw [hrot] at he
      refine ⟨labels j.castSucc,hj,(congrArg (fun a:S.Copy=>a.2.val) he).symm,?_⟩
      have hg:=congrArg (fun a:S.Copy=>a.1) he
      change (C j.castSucc).1*(S.generator (labels j.castSucc))⁻¹=(C j.succ).1 at hg
      rw [←hg]
      group
    closing:=by
      obtain ⟨hj,he⟩:=hCross (Fin.last N)
      rw [finRotate_last] at he
      refine ⟨labels (Fin.last N),hj,(congrArg (fun a:S.Copy=>a.2.val) he).symm,?_⟩
      have hg:=congrArg (fun a:S.Copy=>a.1) he
      change (C (Fin.last N)).1*(S.generator (labels (Fin.last N)))⁻¹=(C 0).1 at hg
      rw [←hg]
      group
    covers:=by
      have hC:∀j:Fin (N+1),S.vertexCyclePiece (C j) r=
          (nativeAngularWalkWord A j.val '' P.carrier)∩Metric.ball (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) r:=fun j=>hPiece j P.carrier
      exact (iUnion_congr hC).trans hCover
    nonoverlap:=by
      intro j k hjk
      change Disjoint ((fun x:ℍ=>(C j).1.val x) '' (P.interior∩Metric.ball (C j).2.val r))
        ((fun x:ℍ=>(C k).1.val x) '' (P.interior∩Metric.ball (C k).2.val r))
      rw [hPiece j P.interior,hPiece k P.interior]
      exact hDis hjk }
  have hIndexRotate (j:Fin (N+1)):
      τ^[(finRotate (N+1) j).val] i=τ (τ^[j.val] i):=by
    refine Fin.lastCases ?_ (fun k=>?_) j
    · rw [finRotate_last]
      change i=τ (τ^[N] i)
      simpa only [Function.iterate_succ_apply'] using hCycle.symm
    · have hrot:finRotate (N+1) k.castSucc=k.succ:=finRotate_of_lt k.isLt
      rw [hrot]
      exact Function.iterate_succ_apply' τ k.val i
  refine ⟨hx,r,c,⟨{side:=labels,crossing:=hCross,turns:=?_}⟩⟩
  intro j
  change E (τ^[j.val] i)≠S.paired (E (τ^[((finRotate (N+1)).symm j).val] i))
  rw [cofiniteTangentialJordanSidePairing_paired_index]
  apply E.injective.ne
  intro he
  have hr:=hIndexRotate ((finRotate (N+1)).symm j)
  rw [(finRotate (N+1)).apply_symm_apply] at hr
  change τ^[j.val] i=finRotate n (ρ (τ^[((finRotate (N+1)).symm j).val] i)) at hr
  rw [←he] at hr
  exact Q.next_ne_self (τ^[j.val] i) hr.symm


/-- Every actual native corner of the mixed polygon has positive original angle. -/
theorem cofiniteTangential_native_vertex_positive {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (i:Fin n) (x:ℍ)
    (hx:(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)) :
    0<θ i := by
  by_contra hn
  have he:θ i=0:=le_antisymm (le_of_not_gt hn) (hθ i).1
  have hIdeal:=cofiniteTangential_zero_vertex_ideal θ d hθ hd i he
  change ‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).vertices i:ℂ)‖=1 at hIdeal
  rw [hx] at hIdeal
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x).norm_lt_one.ne hIdeal


/--
Actual finite vertex periods and the original side geometry prove local tessellation on
the whole native plane, even with genuine ideal vertices outside that plane.
-/
theorem cofiniteTangential_mixed_local_tessellation {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,0<θ i→∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) :
    (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).FiniteFiberLocalTessellationCondition := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
  let S:=cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
  let V:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q
  let G:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_native_geometry Q
  let :IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hNatural:S.NaturalVertexCycleCondition V:=by
    intro x hx
    obtain ⟨i,hi⟩:=hx
    have hpos:=cofiniteTangential_native_vertex_positive θ d hθ hd hb i x.val hi
    obtain ⟨N,hN,hCycle,hAngle⟩:=hPeriod i hpos
    rcases N with _|N
    · omega
    · obtain ⟨hp,r,c,hL⟩:=cofiniteTangential_mixed_natural_vertex_cycle θ d hθ hd hb ρ hρ hθρ i N hN hCycle hAngle
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x.val) hi
      have hpoint:(⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x.val),hp⟩:P.Point)=x:=
        Subtype.ext (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc x.val)
      have hh:∃r:ℝ,∃c:S.VertexCycle {p:P.Point|p.val∈V}
          ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x.val),hp⟩ r,Nonempty (c.NaturalLabels S):=⟨r,c,hL⟩
      exact hpoint ▸ hh
  have hTwo:∀x∈V,∀s t:P.Side,s≠t→x∈s.val→x∈t.val→
      ∀v:P.Side,x∈v.val→v=s∨v=t:=by
    intro x hx s t hst hs ht v hv
    obtain ⟨i,hi⟩:=hx
    have hlabels (a:P.Side) (ha:x∈a.val):
        a=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q ((finRotate n).symm i) ∨a=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i:=by
      have h:=cofiniteJordan_vertex_side_labels Q i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) hi a
        (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using ha)
      exact h
    rcases hlabels s hs with hsl|hsr
    · rcases hlabels t ht with htl|htr
      · exact (hst (hsl.trans htl.symm)).elim
      · exact (hlabels v hv).imp (fun h=>h.trans hsl.symm) (fun h=>h.trans htr.symm)
    · rcases hlabels t ht with htl|htr
      · exact (hlabels v hv).symm.imp (fun h=>h.trans hsr.symm) (fun h=>h.trans htl.symm)
      · exact (hst (hsr.trans htr.symm)).elim
  have hReg:∀x:P.Point,x.val∉V→x.val∈P.interior∨∃s r,S.PairedSideNeighborhood x s r:=by
    apply G.regularity_of_vertex_preservation S
    · exact cofiniteJordan_pairing_preserves_vertices Q S
    · exact cofiniteTangential_jordan_all_opposite_side_neighborhoods θ d hθ hd hb ρ hρ hθρ
  exact hNatural.finiteFiberLocalTessellationCondition S V G.vertex_discrete G.locallyFinite G.side_closed
    G.interior_open (le_of_eq G.carrier_closure) hTwo hReg

end LowDimensionalTopology.Geometry.Fuchsian





namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The literal finite-corner angular periods are internal consequences of the
prescribed mixed signature. Zero entries remain ideal and require no native cycle. -/
theorem cofiniteConstruction_mixed_angular_periods (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,m=0∨2≤m) (hlast:last=0∨2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) :
    ∀i:Fin (cofiniteConstructionAngles g ms last).length,
      0<(cofiniteConstructionAngles g ms last)[i]→∃N:ℕ,3≤N ∧
        ((cofiniteConstructionVertexStep g ms last)^[N]) i=i ∧
        (cofiniteConstructionAngles g ms last)[i]=2*Real.pi/(N:ℝ) := by
  let B:=4*g+ms.length
  let τ:=cofiniteConstructionVertexStep g ms last
  have hB:2≤B:=cofiniteConstruction_base_count g ms last hdef
  intro i hi
  obtain ⟨label,rfl⟩:=(cofiniteConstructionCornerLabelEquiv g ms last hB).surjective i
  cases label with
  | inl a=>
    rw [cofiniteConstructionCornerLabelEquiv_base] at hi ⊢
    have hl:2≤last:=by
      rcases hlast with hl|hl
      · rw [cofiniteConstructionBaseIndex_angle] at hi
        simp only [cofiniteConstructionBaseAngle,cofiniteConstructionConeAngle,hl,Nat.cast_zero,
          div_zero,zero_div,lt_self_iff_false] at hi
      · exact hl
    have hN:4≤B*last:=by simpa using Nat.mul_le_mul hB hl
    refine ⟨B*last,by omega,?_,?_⟩
    · have hBase:τ^[B] (cofiniteConstructionBaseIndex g ms last a)=cofiniteConstructionBaseIndex g ms last a:=
        cofiniteConstructionBaseIndex_full_turn g ms last a
      have hMany:∀k:ℕ,τ^[B*k] (cofiniteConstructionBaseIndex g ms last a)=
          cofiniteConstructionBaseIndex g ms last a:=by
        intro k
        induction k with
        | zero=>rfl
        | succ k ih=>rw [Nat.mul_succ,Function.iterate_add_apply,hBase,ih]
      exact hMany last
    · rw [cofiniteConstructionBaseIndex_angle]
      dsimp only [cofiniteConstructionBaseAngle,cofiniteConstructionConeAngle,B]
      push_cast
      rw [div_div]
      congr 1
      ring
  | inr j=>
    rw [cofiniteConstructionCornerLabelEquiv_outer] at hi ⊢
    have hm:2≤ms[j.val]:=by
      rcases hms _ (List.getElem_mem j.val.isLt) with hm|hm
      · rw [cofiniteConstructionOuterIndex_angle] at hi
        change 0<2*Real.pi/(ms[j.val.val]:ℝ) at hi
        change ms[j.val.val]=0 at hm
        rw [hm,Nat.cast_zero,div_zero] at hi
        exact (lt_irrefl (0:ℝ) hi).elim
      · exact hm
    have hm3:3≤ms[j.val]:=by have:=j.property;omega
    refine ⟨ms[j.val],hm3,?_,?_⟩
    · have hFix:τ (cofiniteConstructionOuterIndex g ms last j)=
          cofiniteConstructionOuterIndex g ms last j:=cofiniteConstructionOuterIndex_fixed g ms last j
      have hMany:∀k:ℕ,τ^[k] (cofiniteConstructionOuterIndex g ms last j)=
          cofiniteConstructionOuterIndex g ms last j:=by
        intro k
        induction k with
        | zero=>rfl
        | succ k ih=>rw [Function.iterate_succ_apply,hFix,ih]
      exact hMany _
    · rw [cofiniteConstructionOuterIndex_angle]
      rfl


/--
The actual original polygon and original side maps satisfy local tessellation for every
allowed signature, including all zero-order cusp entries. No global covering,
discreteness, fundamental-domain or uniform-radius assumption is used here.
-/
theorem cofiniteConstruction_mixed_local_tessellation (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,m=0∨2≤m) (hlast:last=0∨2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i=>(cofiniteConstructionAngles g ms last)[i]) d=Real.pi) :
    let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=
      fun i=>(cofiniteConstructionAngles g ms last)[i]
    let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
      hms hlast hdef _ (List.getElem_mem i.isLt)
    (cofiniteTangentialSidePairing θ d hθ hd hb (cofiniteConstructionPairing g ms last)
      (cofiniteConstructionPairing_involutive g ms last)
      (cofiniteConstructionPairing_angle_profile g ms last)).FiniteFiberLocalTessellationCondition := by
  dsimp only
  apply cofiniteTangential_mixed_local_tessellation
  intro i hi
  exact cofiniteConstruction_mixed_angular_periods g ms last hms hlast hdef i hi

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual compactified native SL action has its original sphere value
in the compactified half-plane coordinate. -/
theorem cofiniteSL_closed_halfPlane_value (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p : 𝕔𝔻) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap p)).val =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius s).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p).val := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGLClosedHalfPlaneHomeomorph (Matrix.SpecialLinearGroup.mapGL ℝ s) _
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p)))).val = _
  rw [Homeomorph.symm_apply_apply]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius, MonoidHom.comp_apply, _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_matrix]
  rfl

/-- Every genuine ideal corner has a positive native normalizer which also
fixes the original common incircle center I. -/
theorem cofiniteSL_centered_ideal_normalizer (p : 𝕔𝔻) (hp : ‖(p : ℂ)‖ = 1) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ, s • UpperHalfPlane.I = UpperHalfPlane.I ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap p = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint := by
  obtain ⟨a, ha⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discIdealPoint_exists_SL_normalizer p hp
  let z : ℍ := a • UpperHalfPlane.I
  let s := z.toSL2R⁻¹ * a
  have hInf : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (z.toSL2R⁻¹)).val ∞ = ∞ := by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff _).mpr
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, UpperHalfPlane.coe_toSL2R]
  have ha' : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius a).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p).val = ∞ := by
    rw [← cofiniteSL_closed_halfPlane_value, ha, Homeomorph.symm_apply_apply]
    rfl
  refine ⟨s, ?_, ?_⟩
  · dsimp only [s]
    rw [mul_smul]
    rw [show a • UpperHalfPlane.I = z.toSL2R • UpperHalfPlane.I by
      rw [UpperHalfPlane.toSL2R_smul_I]]
    exact inv_smul_smul _ _
  · apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm.injective
    apply Subtype.ext
    rw [cofiniteSL_closed_halfPlane_value, Homeomorph.symm_apply_apply]
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (z.toSL2R⁻¹ * a)).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p).val = ∞
    rw [map_mul]
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (z.toSL2R⁻¹)).val
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius a).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p).val) = ∞
    rw [ha', hInf]

/-- A genuine centered positive native map is one common complex rotation
on all finite and ideal points, including their actual closed Klein coordinates. -/
theorem cofiniteSL_centered_closed_rotation (s : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hs : s • UpperHalfPlane.I = UpperHalfPlane.I) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      (∀ p : 𝕔𝔻, ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap p : ℂ) = u * (p : ℂ)) ∧
      ∀ p : 𝕔𝔻, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap p) =
        u * _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p := by
  obtain ⟨a, b, hab, rfl⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_fix_I_rotation s hs
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier a b
  have hu : ‖u‖ = 1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationMultiplier_norm a b hab
  have he : (fun p : 𝕔𝔻 => ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hab)).closedMap p : ℂ)) =
      (fun p : 𝕔𝔻 => u * (p : ℂ)) := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.denseRange_discToClosedModel.equalizer
      (Complex.UnitClosedDisc.continuous_coe.comp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry _).closedMap.continuous)
      (continuous_const.mul Complex.UnitClosedDisc.continuous_coe)
    funext z
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hab)).closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) : ℂ) =
      u * (z : ℂ)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes]
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hab) z : ℂ) = u * (z : ℂ)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL_disc_action, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation_coe]
  refine ⟨u, hu, fun p => congrFun he p, ?_⟩
  intro p
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hab)).closedMap p : ℂ) =
    u * _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (p : ℂ)
  rw [congrFun he p, _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula, _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula, norm_mul, hu, one_mul]
  ring

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Each original native support has the literal ordered incircle equation,
without any finiteness restriction on its original endpoints. -/
theorem cofiniteTangential_native_support_equation {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n) (x : ℍ) :
    x ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i).carrier ↔
      inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x) = Real.tanh d := by
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S := _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  have hline : Q.geodesicSide i = S.supportLine i := by
    apply (Q.geodesicSide i).eq_of_two_closed_points (S.supportLine i)
      (Q.vertices_injective.ne (Q.next_ne_self i).symm)
      (Q.geodesicSide_endpoints i).1 (Q.geodesicSide_endpoints i).2
    · exact (S.incident_mem_support i).1
    · exact (S.incident_mem_support i).2
  change x ∈ (Q.geodesicSide i).toHalfPlane.carrier ↔ _
  rw [hline]
  have hmem := ((S.supportLine i).mem_carrier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)).symm
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] at hmem
  exact hmem.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_equation_iff _ _ _ _ _)

/-- Every centered positive normalizer of the actual zero-angle corner
puts its original incoming and outgoing supports at the same signed height scale. -/
theorem cofiniteTangential_zero_support_normalization {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n) (hi : θ i = 0)
    (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs : s • UpperHalfPlane.I = UpperHalfPlane.I)
    (hp : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) :
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) ((finRotate n).symm i)).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ s) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (Real.sinh d) ∧
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ s) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (-Real.sinh d) := by
  obtain ⟨u, hu, hcoe, hK⟩ := cofiniteSL_centered_closed_rotation s hs
  have htarget : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint : ℂ) = 1 := by
    apply OnePoint.coe_injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_toExtended]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty
  have htargetK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) = 1 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint : ℂ) = 1
    rw [htarget]
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  have hcoord : _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate (θ i) d = 1 :=
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_eq_one_iff (hθ i) hd).mpr hi
  have hmarked : u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i) = 1 := by
    have h := hK (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)
    rw [hp, htargetK, _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_coordinate, hcoord, one_smul] at h
    exact h.symm
  have hU : u = conj (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i)) := by
    apply mul_right_cancel₀ (show _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i) ≠ 0 from
      norm_ne_zero_iff.mp (by rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm]; norm_num))
    rw [hmarked, Complex.conj_mul', _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm]
    norm_num
  have hsub (a b : ℝ) : conj (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit a) * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit b = _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (b - a) := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_re, _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_im, Real.cos_sub, Real.sin_sub] <;> ring
  have hcos : Real.cos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d) = Real.tanh d := by
    have hc := (div_eq_iff (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_cos_pos (hθ i) hd).ne').mp hcoord
    simpa only [one_mul] using hc.symm
  have hsin : Real.sin (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d) = 1 / Real.cosh d := by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_sin (hθ i), hi]
    norm_num
  have hnormalIn : u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i) =
      (⟨Real.tanh d, -(1 / Real.cosh d)⟩ : ℂ) := by
    rw [hU, hsub]
    rw [show _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i - _root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i =
      -_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d by rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle]; ring]
    apply Complex.ext <;> simp only [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_re, _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_im,
      Real.cos_neg, Real.sin_neg, hcos, hsin]
  have hnormalOut : u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i)) =
      (⟨Real.tanh d, 1 / Real.cosh d⟩ : ℂ) := by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_unit_next θ d hb i, hU, hsub, _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_succ]
    rw [show _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i + 2 * _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d -
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i = _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d by
      rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle]; ring]
    apply Complex.ext <;> simp only [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_re, _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_im,
      hcos, hsin]
  have hunit : conj u * u = 1 := by rw [Complex.conj_mul', hu]; norm_num
  have hinner (a b : ℂ) : inner ℝ (u * a) (u * b) = inner ℝ a b := by
    rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, RCLike.inner_apply', RCLike.inner_apply']
    change (conj (u * a) * (u * b)).re = (conj a * b).re
    rw [map_mul]
    have he : (conj u * conj a) * (u * b) = (conj u * u) * (conj a * b) := by ring
    rw [he, hunit, one_mul]
  have hKx (x : ℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x =
      u * _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (s⁻¹ • x) := by
    have h := hK (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s⁻¹ • x)))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] at h
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s⁻¹ • x)))) = _ at h
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc, smul_inv_smul] at h
    exact h
  have himage (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (x : ℍ) :
      x ∈ (L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ s)).carrier ↔ s⁻¹ • x ∈ L.carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    constructor
    · rintro ⟨y, hy, hxy⟩
      change s • y = x at hxy
      rw [← hxy, inv_smul_smul]
      exact hy
    · intro hx
      exact ⟨s⁻¹ • x, hx, smul_inv_smul s x⟩
  have hcut (ε : ℝ) (hε : ε ^ 2 = 1) (x : ℍ) :
      inner ℝ (⟨Real.tanh d, ε / Real.cosh d⟩ : ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x) = Real.tanh d ↔
        x.re = -ε * Real.sinh d := by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit]
    dsimp only
    rw [Real.tanh_eq_sinh_div_cosh]
    have hden : x.re ^ 2 + x.im ^ 2 + 1 ≠ 0 := by positivity
    have hch : Real.cosh d ≠ 0 := (Real.cosh_pos d).ne'
    field_simp [hden, hch]
    constructor
    · intro h
      have hlin : ε * x.re = -Real.sinh d := by nlinarith only [h]
      calc
        x.re = ε ^ 2 * x.re := by rw [hε, one_mul]
        _ = ε * (ε * x.re) := by ring
        _ = -(Real.sinh d * ε) := by rw [hlin]; ring
    · intro h
      rw [h]
      have heq : Real.sinh d * ε ^ 2 = Real.sinh d := by rw [hε, mul_one]
      nlinarith only [heq]
  constructor
  · apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    ext x
    rw [himage, cofiniteTangential_native_support_equation, Equiv.apply_symm_apply]
    rw [← hinner, ← hKx, hnormalIn]
    change _ ↔ x.re = Real.sinh d
    simpa only [neg_div, neg_neg, one_mul] using hcut (-1) (by norm_num) x
  · apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    ext x
    rw [himage, cofiniteTangential_native_support_equation]
    rw [← hinner, ← hKx, hnormalOut]
    change _ ↔ x.re = -Real.sinh d
    simpa only [one_div, neg_one_mul] using hcut 1 (by norm_num) x

/-- The signed common-height frame is supplied by the genuine zero-angle
corner and its actual original supports, rather than assumed as chart data. -/
theorem cofiniteTangential_zero_support_frames {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n) (hi : θ i = 0) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ, s • UpperHalfPlane.I = UpperHalfPlane.I ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint ∧
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) ((finRotate n).symm i)).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ s) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (Real.sinh d) ∧
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ s) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (-Real.sinh d) := by
  obtain ⟨s, hs, hp⟩ := cofiniteSL_centered_ideal_normalizer _
    ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_ideal_iff θ d hθ hd i).mpr hi)
  exact ⟨s, hs, hp, cofiniteTangential_zero_support_normalization θ d hθ hd hb i hi s hs hp⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual closed native tile retains every original literal support cut. -/
theorem cofiniteTangential_jordan_carrier_literal_iff {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (z : ℍ) :
    z ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).carrier ↔
      ∀ j, inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n j)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) ≤ Real.tanh d := by
  let S := _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  rw [cofiniteJordan_carrier_iff]
  have hBody := S.closedModelClosure_image
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ S.toDiscPolygon.closedCarrier ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) ∈ S.kleinRegion := by
    rw [← hBody]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.symm
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ S.toDiscPolygon.closedCarrier ↔ _
  rw [he, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
  rfl

/-- The actual open native tile retains every original strict support cut. -/
theorem cofiniteTangential_jordan_interior_literal_iff {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (z : ℍ) :
    z ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).interior ↔
      ∀ j, inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n j)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) < Real.tanh d := by
  let S := _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z ∈ S.toDiscPolygon.interior ↔ _
  rw [S.toDiscPolygon_interior]
  rfl

/-- The whole native high horoball approaches the true ideal Klein point one,
uniformly in its real coordinate. -/
theorem cofinite_halfPlaneKlein_distance_one (z : ℍ) :
    ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z - 1‖ ≤ 1 / z.im := by
  let D : ℝ := z.re ^ 2 + z.im ^ 2 + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  have heq : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z - 1‖ ^ 2 = 4 * (1 + z.re ^ 2) / D ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
    dsimp only [D]
    field_simp
    ring
  have hnum : 4 * (1 + z.re ^ 2) * z.im ^ 2 ≤ D ^ 2 := by
    dsimp only [D]
    nlinarith [sq_nonneg (z.re ^ 2 + 1 - z.im ^ 2)]
  have hsq : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z - 1‖ ^ 2 ≤ (1 / z.im) ^ 2 := by
    rw [heq, div_pow, one_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos z.im_pos)).mpr
    simpa only [one_mul] using hnum
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- The actual centered zero-corner frame carries the two original normals
to their exact signed incircle directions. -/
theorem cofiniteTangential_zero_frame_normal_coordinates {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n) (hi : θ i = 0)
    (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs : s • UpperHalfPlane.I = UpperHalfPlane.I)
    (hp : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      (∀ p : 𝕔𝔻, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap p) =
        u * _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) ∧
      u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i) =
        (⟨Real.tanh d, -(1 / Real.cosh d)⟩ : ℂ) ∧
      u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i)) =
        (⟨Real.tanh d, 1 / Real.cosh d⟩ : ℂ) := by
  obtain ⟨u, hu, hcoe, hK⟩ := cofiniteSL_centered_closed_rotation s hs
  have htarget : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint : ℂ) = 1 := by
    apply OnePoint.coe_injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_toExtended]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty
  have htargetK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) = 1 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint : ℂ) = 1
    rw [htarget]
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  have hcoord : _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate (θ i) d = 1 :=
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_eq_one_iff (hθ i) hd).mpr hi
  have hmarked : u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i) = 1 := by
    have h := hK (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)
    rw [hp, htargetK, _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_coordinate, hcoord, one_smul] at h
    exact h.symm
  have hU : u = conj (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i)) := by
    apply mul_right_cancel₀ (show _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i) ≠ 0 from
      norm_ne_zero_iff.mp (by rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm]; norm_num))
    rw [hmarked, Complex.conj_mul', _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm]
    norm_num
  have hsub (a b : ℝ) : conj (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit a) * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit b = _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (b - a) := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_re, _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_im, Real.cos_sub, Real.sin_sub] <;> ring
  have hcos : Real.cos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d) = Real.tanh d := by
    have hc := (div_eq_iff (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_cos_pos (hθ i) hd).ne').mp hcoord
    simpa only [one_mul] using hc.symm
  have hsin : Real.sin (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d) = 1 / Real.cosh d := by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_sin (hθ i), hi]
    norm_num
  have hnormalIn : u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i) =
      (⟨Real.tanh d, -(1 / Real.cosh d)⟩ : ℂ) := by
    rw [hU, hsub]
    rw [show _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i - _root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i =
      -_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d by rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle]; ring]
    apply Complex.ext <;> simp only [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_re, _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_im,
      Real.cos_neg, Real.sin_neg, hcos, hsin]
  have hnormalOut : u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i)) =
      (⟨Real.tanh d, 1 / Real.cosh d⟩ : ℂ) := by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_unit_next θ d hb i, hU, hsub, _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_succ]
    rw [show _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i + 2 * _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d -
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle θ d i = _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d by
      rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle]; ring]
    apply Complex.ext <;> simp only [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_re, _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_im,
      hcos, hsin]
  exact ⟨u, hu, hK, hnormalIn, hnormalOut⟩

/-- In the actual signed zero-corner frame, the genuine original closed tile
and genuine original open interior are exactly their deep vertical cusp strips. -/
theorem cofiniteTangential_zero_deep_strip {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n) (hi : θ i = 0)
    (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs : s • UpperHalfPlane.I = UpperHalfPlane.I)
    (hp : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ z : ℍ, Y < z.im →
      (s⁻¹ • z ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).carrier ↔
        -Real.sinh d ≤ z.re ∧ z.re ≤ Real.sinh d) ∧
      (s⁻¹ • z ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).interior ↔
        -Real.sinh d < z.re ∧ z.re < Real.sinh d) := by
  obtain ⟨u, hu, hK, hnIn, hnOut⟩ :=
    cofiniteTangential_zero_frame_normal_coordinates θ d hθ hd hb i hi s hs hp
  let S := _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedSupportData θ d hθ hd hb
  let N : Fin n → ℂ := fun j => u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n j))
  have hunit : conj u * u = 1 := by rw [Complex.conj_mul', hu]; norm_num
  have hinner (a b : ℂ) : inner ℝ (u * a) (u * b) = inner ℝ a b := by
    rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, RCLike.inner_apply', RCLike.inner_apply']
    change (conj (u * a) * (u * b)).re = (conj a * b).re
    rw [map_mul]
    have he : (conj u * conj a) * (u * b) = (conj u * u) * (conj a * b) := by ring
    rw [he, hunit, one_mul]
  have hKx (z : ℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z =
      u * _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (s⁻¹ • z) := by
    have h := hK (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s⁻¹ • z)))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] at h
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s⁻¹ • z)))) = _ at h
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc, smul_inv_smul] at h
    exact h
  have htransport (j : Fin n) (z : ℍ) :
      inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n j)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (s⁻¹ • z)) = inner ℝ (N j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) := by
    change _ = inner ℝ (u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n j)))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)
    rw [hKx z, hinner]
  have htarget : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint : ℂ) = 1 := by
    apply OnePoint.coe_injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_toExtended]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty
  have hmarked : u * _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) = 1 := by
    have h := hK (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)
    rw [hp] at h
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint : ℂ) = _ at h
    rw [htarget] at h
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula] at h
    exact h.symm
  have hnon (j : Fin n) (hjprev : j ≠ (finRotate n).symm i) (hji : j ≠ i) :
      inner ℝ (N j) 1 < Real.tanh d := by
    rw [← hmarked, hinner]
    exact S.nonincident j i (Ne.symm hji) (fun he => hjprev (by
      apply (finRotate n).injective
      rw [Equiv.apply_symm_apply]
      exact he.symm))
  let U : Set ℂ := ⋂ j : Fin n, if j = (finRotate n).symm i ∨ j = i then univ else
    {w | inner ℝ (N j) w < Real.tanh d}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro j
    split_ifs
    · exact isOpen_univ
    · exact isOpen_lt (continuous_const.inner continuous_id) continuous_const
  have hOne : (1 : ℂ) ∈ U := by
    apply mem_iInter.mpr
    intro j
    by_cases hj : j = (finRotate n).symm i ∨ j = i
    · simp only [hj, ite_true, mem_univ]
    · simp only [hj, ite_false, mem_ofPred_eq]
      exact hnon j (fun h => hj (Or.inl h)) (fun h => hj (Or.inr h))
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hOne)
  refine ⟨max 1 (1 / ε), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  have hy : 1 / ε < z.im := lt_of_le_of_lt (le_max_right _ _) hz
  have hInv : 1 / z.im < ε := by
    apply (div_lt_iff₀ z.im_pos).mpr
    have h := (div_lt_iff₀ hε).mp hy
    linarith
  have hzU : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z ∈ U := by
    apply hεU
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt (cofinite_halfPlaneKlein_distance_one z) hInv
  have hOthers (j : Fin n) (hjprev : j ≠ (finRotate n).symm i) (hji : j ≠ i) :
      inner ℝ (N j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) < Real.tanh d := by
    have h := mem_iInter.mp hzU j
    have hj : ¬(j = (finRotate n).symm i ∨ j = i) := fun h => h.elim hjprev hji
    simpa only [hj, ite_false, mem_ofPred_eq] using h
  have hnPrev : N ((finRotate n).symm i) = (⟨Real.tanh d, -(1 / Real.cosh d)⟩ : ℂ) := by
    dsimp only [N]
    rw [Equiv.apply_symm_apply]
    exact hnIn
  have hDiff (a : ℝ) :
      inner ℝ (⟨Real.tanh d, a / Real.cosh d⟩ : ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) - Real.tanh d =
        -(2 / (Real.cosh d * (z.re ^ 2 + z.im ^ 2 + 1))) * (Real.sinh d + a * z.re) := by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit]
    dsimp only
    rw [Real.tanh_eq_sinh_div_cosh]
    have hden : z.re ^ 2 + z.im ^ 2 + 1 ≠ 0 := by positivity
    field_simp [hden, (Real.cosh_pos d).ne']
    ring
  have hpos : 0 < 2 / (Real.cosh d * (z.re ^ 2 + z.im ^ 2 + 1)) := by positivity
  have hLe (a : ℝ) :
      inner ℝ (⟨Real.tanh d, a / Real.cosh d⟩ : ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) ≤ Real.tanh d ↔
        -Real.sinh d ≤ a * z.re := by
    rw [← sub_nonpos, hDiff, neg_mul, neg_nonpos, mul_nonneg_iff_of_pos_left hpos]
    constructor <;> intro h <;> linarith
  have hLt (a : ℝ) :
      inner ℝ (⟨Real.tanh d, a / Real.cosh d⟩ : ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) < Real.tanh d ↔
        -Real.sinh d < a * z.re := by
    rw [← sub_lt_zero, hDiff, neg_mul, neg_lt_zero, mul_pos_iff_of_pos_left hpos]
    constructor <;> intro h <;> linarith
  have hinLe : inner ℝ (N ((finRotate n).symm i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) ≤ Real.tanh d ↔
      z.re ≤ Real.sinh d := by
    rw [hnPrev]
    simpa only [neg_div, one_div, neg_one_mul, neg_le_neg_iff] using hLe (-1)
  have houtLe : inner ℝ (N i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) ≤ Real.tanh d ↔
      -Real.sinh d ≤ z.re := by
    change inner ℝ (u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i))) _ ≤ _ ↔ _
    rw [hnOut]
    simpa only [one_div, one_mul] using hLe 1
  have hinLt : inner ℝ (N ((finRotate n).symm i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) < Real.tanh d ↔
      z.re < Real.sinh d := by
    rw [hnPrev]
    simpa only [neg_div, one_div, neg_one_mul, neg_lt_neg_iff] using hLt (-1)
  have houtLt : inner ℝ (N i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) < Real.tanh d ↔
      -Real.sinh d < z.re := by
    change inner ℝ (u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i))) _ < _ ↔ _
    rw [hnOut]
    simpa only [one_div, one_mul] using hLt 1
  constructor
  · rw [cofiniteTangential_jordan_carrier_literal_iff]
    simp_rw [htransport]
    constructor
    · intro h
      exact ⟨houtLe.mp (h i), hinLe.mp (h ((finRotate n).symm i))⟩
    · rintro ⟨hl, hr⟩ j
      by_cases hjp : j = (finRotate n).symm i
      · subst j; exact hinLe.mpr hr
      by_cases hji : j = i
      · subst j; exact houtLe.mpr hl
      exact (hOthers j hjp hji).le
  · rw [cofiniteTangential_jordan_interior_literal_iff]
    simp_rw [htransport]
    constructor
    · intro h
      exact ⟨houtLt.mp (h i), hinLt.mp (h ((finRotate n).symm i))⟩
    · rintro ⟨hl, hr⟩ j
      by_cases hjp : j = (finRotate n).symm i
      · subst j; exact hinLt.mpr hr
      by_cases hji : j = i
      · subst j; exact houtLt.mpr hl
      exact hOthers j hjp hji

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Topology

/-- An ideal point in the actual closed polygon is one of its original vertices. -/
theorem cofiniteJordan_ideal_carrier_vertex {n:ℕ} (Q:_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (p:𝕔𝔻)
    (hp:p∈Q.closedCarrier) (hn:‖(p:ℂ)‖=1) :∃i:Fin n,Q.vertices i=p := by
  have hc:(p:ℂ)∈closure Q.complexInterior:=by
    rw [←Q.closedCarrier_complex_image]
    exact mem_image_of_mem _ hp
  rw [Q.closure_complexInterior] at hc
  have hb:p∈Q.boundary:=by
    rcases hc with hc|hc
    · have hh:=Q.complexInterior_subset_disc hc
      rw [Metric.mem_ball,dist_zero_right,hn] at hh
      exact (lt_irrefl (1:ℝ) hh).elim
    · obtain ⟨q,hq,hqp⟩:=hc
      have hqp':q=p:=Subtype.ext hqp
      exact hqp' ▸ hq
  obtain ⟨i,hi⟩:=mem_iUnion.mp hb
  have hHull:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈convexHull ℝ
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices i),_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices (finRotate n i))}:Set ℂ):=by
    rw [convexHull_pair,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hi
  have hSub:convexHull ℝ
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices i),_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices (finRotate n i))}:Set ℂ)⊆
        Metric.closedBall (0:ℂ) 1:=by
    apply convexHull_min ?_ (convex_closedBall (0:ℂ) 1)
    rintro q (rfl|rfl) <;> exact mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein _).norm_le_one
  have hext:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈(Metric.closedBall (0:ℂ) 1).extremePoints ℝ:=by
    apply StrictConvexSpace.sphere_subset_extremePoints_closedBall (0:ℂ) one_ne_zero
    exact mem_sphere_zero_iff_norm.mpr ((_root_.LowDimensionalTopology.Geometry.Polygon.norm_closedKleinCoordinate_eq_one_iff p).mpr hn)
  have hh:=inter_extremePoints_subset_extremePoints_of_subset hSub ⟨hHull,hext⟩
  have hq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices i),_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices (finRotate n i))}:Set ℂ):=
    extremePoints_convexHull_subset hh
  rcases hq with hq|hq
  · exact ⟨i,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective hq).symm⟩
  · exact ⟨finRotate n i,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective hq).symm⟩


/-- The whole original polygon lies between its two actual signed cusp supports,
not only the part sufficiently deep in the cusp. -/
theorem cofiniteTangential_zero_global_strip {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (i:Fin n) (hi:θ i=0) (s:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hs:s • UpperHalfPlane.I=UpperHalfPlane.I)
    (hp:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) (x:ℍ)
    (hx:x∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).carrier) :
    -Real.sinh d≤(s • x).re ∧(s • x).re≤Real.sinh d := by
  obtain ⟨u, hu, hK, hnIn, hnOut⟩ :=
    cofiniteTangential_zero_frame_normal_coordinates θ d hθ hd hb i hi s hs hp
  let N : Fin n → ℂ := fun j => u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n j))
  have hunit : conj u * u = 1 := by rw [Complex.conj_mul', hu]; norm_num
  have hinner (a b : ℂ) : inner ℝ (u * a) (u * b) = inner ℝ a b := by
    rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, RCLike.inner_apply', RCLike.inner_apply']
    change (conj (u * a) * (u * b)).re = (conj a * b).re
    rw [map_mul]
    have he : (conj u * conj a) * (u * b) = (conj u * u) * (conj a * b) := by ring
    rw [he, hunit, one_mul]
  have hKx (z : ℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z =
      u * _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (s⁻¹ • z) := by
    have h := hK (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s⁻¹ • z)))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] at h
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s⁻¹ • z)))) = _ at h
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc, smul_inv_smul] at h
    exact h
  have htransport (j : Fin n) (z : ℍ) :
      inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n j)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (s⁻¹ • z)) = inner ℝ (N j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) := by
    change _ = inner ℝ (u * _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n j)))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)
    rw [hKx z, hinner]
  let z:ℍ:=s • x
  have hnPrev : N ((finRotate n).symm i) = (⟨Real.tanh d, -(1 / Real.cosh d)⟩ : ℂ) := by
    dsimp only [N]
    rw [Equiv.apply_symm_apply]
    exact hnIn
  have hDiff (a : ℝ) :
      inner ℝ (⟨Real.tanh d, a / Real.cosh d⟩ : ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) - Real.tanh d =
        -(2 / (Real.cosh d * (z.re ^ 2 + z.im ^ 2 + 1))) * (Real.sinh d + a * z.re) := by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit]
    dsimp only
    rw [Real.tanh_eq_sinh_div_cosh]
    have hden : z.re ^ 2 + z.im ^ 2 + 1 ≠ 0 := by positivity
    field_simp [hden, (Real.cosh_pos d).ne']
    ring
  have hpos : 0 < 2 / (Real.cosh d * (z.re ^ 2 + z.im ^ 2 + 1)) := by positivity
  have hLe (a : ℝ) :
      inner ℝ (⟨Real.tanh d, a / Real.cosh d⟩ : ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) ≤ Real.tanh d ↔
        -Real.sinh d ≤ a * z.re := by
    rw [← sub_nonpos, hDiff, neg_mul, neg_nonpos, mul_nonneg_iff_of_pos_left hpos]
    constructor <;> intro h <;> linarith
  have hc:∀j:Fin n,inner ℝ (N j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤Real.tanh d:=by
    intro j
    rw [←htransport j z]
    change inner ℝ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n j)))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (s⁻¹ •(s •x)))≤Real.tanh d
    rw [inv_smul_smul]
    exact (cofiniteTangential_jordan_carrier_literal_iff θ d hθ hd hb x).mp hx j
  have hOut:=hc i
  change inner ℝ (u*_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (finRotate n i))) _≤_ at hOut
  rw [hnOut] at hOut
  have hIn:=hc ((finRotate n).symm i)
  rw [hnPrev] at hIn
  constructor
  · simpa only [one_div,one_mul] using (hLe 1).mp hOut
  · have hh: -Real.sinh d≤(-1:ℝ)*z.re :=
      (hLe (-1)).mp (by simpa only [neg_div,one_div] using hIn)
    change z.re≤Real.sinh d
    linarith


/-- Removing sufficiently deep actual cusp ends leaves a genuine compact native
core. Its compactness is proved in the original closed-disc compactification. -/
theorem cofiniteTangential_truncated_core_isCompact {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (F:Fin n→Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hFI:∀i,θ i=0→F i • UpperHalfPlane.I=UpperHalfPlane.I)
    (hFp:∀i,θ i=0→(_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (F i)).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) (Y:ℝ) :
    IsCompact {z:ℍ|z∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).carrier ∧
      ∀i:Fin n,θ i=0→(F i •z).im≤Y} := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
  let K:Set ℍ:={z|z∈P.carrier ∧∀i:Fin n,θ i=0→(F i •z).im≤Y}
  let f:ℍ→𝕔𝔻:=fun z=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)
  have hf:IsEmbedding f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isEmbedding
  have hPclosed:IsClosed P.carrier:=by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier]
    exact isClosed_closure
  have hKclosed:IsClosed K:=by
    change IsClosed (P.carrier∩{z:ℍ|∀i:Fin n,θ i=0→(F i •z).im≤Y})
    apply hPclosed.inter
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro _hi
    exact isClosed_le (UpperHalfPlane.continuous_im.comp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F i)).continuous) continuous_const
  have hclQ:closure (f ''K)⊆Q.closedCarrier:=by
    apply closure_minimal ?_ Q.closedCarrier_isClosed
    rintro _ ⟨z,hz,rfl⟩
    exact (cofiniteJordan_carrier_iff Q z).mp hz.1
  have hRange:closure (f ''K)⊆range f:=by
    intro p hp
    by_cases hfin:‖(p:ℂ)‖<1
    · refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint p hfin),?_⟩
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint p hfin)))=p
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec]
    · have hn:‖(p:ℂ)‖=1:=le_antisymm p.norm_le_one (le_of_not_gt hfin)
      obtain ⟨i,hiv⟩:=cofiniteJordan_ideal_carrier_vertex Q p (hclQ hp) hn
      have hi:θ i=0:=by
        rw [←_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle θ d hθ hd hb i]
        exact Q.angle_of_ideal i (hiv ▸ hn)
      let c:𝕔𝔻→OnePoint ℂ:=fun q=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (F i)).closedMap q)).val
      have hc:Continuous c:=continuous_subtype_val.comp
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm.continuous.comp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (F i)).closedMap.continuous)
      have hcf (z:ℍ):c (f z)=((F i •z:ℍ):ℂ):=by
        dsimp only [c,f]
        rw [cofiniteSL_closed_halfPlane_value,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior,Homeomorph.symm_apply_apply]
        exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action (F i) z
      let B:Set (OnePoint ℂ):=((↑):ℂ→OnePoint ℂ) ''Metric.closedBall (0:ℂ) (Real.sinh d+|Y|)
      have hB:IsClosed B:=(isCompact_closedBall (0:ℂ) (Real.sinh d+|Y|)).image
        OnePoint.continuous_coe |>.isClosed
      have hContain:f ''K⊆c ⁻¹'B:=by
        rintro _ ⟨z,hz,rfl⟩
        change c (f z)∈B
        rw [hcf]
        refine ⟨((F i •z:ℍ):ℂ),mem_closedBall_zero_iff.mpr ?_,rfl⟩
        have hre:|(F i •z).re|≤Real.sinh d:=abs_le.mpr
          (cofiniteTangential_zero_global_strip θ d hθ hd hb i hi (F i) (hFI i hi) (hFp i hi) z hz.1)
        calc
          ‖((F i •z:ℍ):ℂ)‖≤|(F i •z).re|+|(F i •z).im|:=Complex.norm_le_abs_re_add_abs_im _
          _≤Real.sinh d+|Y|:=add_le_add hre (by
            rw [abs_of_pos (F i •z).im_pos]
            exact (hz.2 i hi).trans (le_abs_self Y))
      have hpB:c p∈B:=(closure_minimal hContain (hB.preimage hc)) hp
      have hcp:c p=∞:=by
        dsimp only [c]
        rw [←hiv]
        change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (F i)).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i))).val=∞
        rw [hFp i hi,Homeomorph.symm_apply_apply]
        rfl
      rw [hcp] at hpB
      obtain ⟨z,_hz,hzInf⟩:=hpB
      exact (OnePoint.coe_ne_infty z hzInf).elim
  have hCompact:IsCompact (f ⁻¹'closure (f ''K)):=
    hf.isInducing.isCompact_preimage' isClosed_closure.isCompact hRange
  rw [←hf.closure_eq_preimage_closure_image K,hKclosed.closure_eq] at hCompact
  exact hCompact

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
  Topology

/--
Actual local tessellation charts have a common positive target radius on a genuine compact
subset of the original tile. The source tile itself need not be compact.
-/
theorem nativePoincare_compact_subset_ball_charts {P:_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ}
    (S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (h:S.FiniteFiberLocalTessellationCondition)
    (K:Set ℍ) (hK:IsCompact K) (hKP:K⊆P.carrier) :
    ∃ε:ℝ,0<ε ∧∀x:P.Point,x.val∈K→∃e:OpenPartialHomeomorph S.Development ℍ,
      S.project (1,x)∈e.source ∧e.target=Metric.ball x.val ε ∧
        EqOn e S.evaluation e.source := by
  classical
  let :IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hK':IsCompact ((Subtype.val:P.Point→ℍ) ⁻¹'K):=
    IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK (by
      simpa only [Subtype.range_val] using hKP)
  choose r hr ht using h.local_radius
  have hhalf:∀x:P.Point,S.LocalTessellation (1,x) (r x/2):=by
    intro x
    exact ht x _ (half_pos (hr x)) (by linarith [hr x])
  let U:P.Point→Set P.Point:=fun x=>
    (fun y:P.Point=>S.project (1,y)) ⁻¹'(S.project ''S.copyNeighborhood (1,x) (r x/2))
  have hU:∀x,IsOpen (U x):=fun x=>(hhalf x).isOpen_image S |>.preimage S.continuous_originalCopy
  have hcover:((Subtype.val:P.Point→ℍ) ⁻¹'K)⊆⋃x,U x:=by
    intro x _hx
    exact mem_iUnion.mpr ⟨x,(hhalf x).center_mem S (half_pos (hr x))⟩
  obtain ⟨t,hcover⟩:=hK'.elim_finite_subcover U hU hcover
  obtain ⟨ε,hε,hbound⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.positive_radius_bound t
    (fun x=>r x/2) (fun x _=>half_pos (hr x))
  refine ⟨ε,hε,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩:=mem_iUnion₂.mp (hcover hx)
  have hyx:S.evaluation (S.project (1,x))∈Metric.ball (S.copyEvaluation (1,y)) (r y/2):=by
    rw [←(hhalf y).evaluation_image S]
    exact mem_image_of_mem S.evaluation hxy
  have hdist:dist x.val y.val<r y/2:=by
    change dist ((1:S.Generated) •x.val) ((1:S.Generated) •y.val)<r y/2 at hyx
    simpa only [one_smul] using hyx
  have htFull:S.LocalTessellation (1,y) (r y):=ht y _ (hr y) le_rfl
  have hsource:S.project (1,x)∈S.project ''S.copyNeighborhood (1,y) (r y):=by
    obtain ⟨b,hb,hbx⟩:=hxy
    exact ⟨b,S.copyNeighborhood_mono (1,y) (by linarith [hr y]) hb,hbx⟩
  have hball:Metric.ball (S.evaluation (S.project (1,x))) ε⊆Metric.ball (S.copyEvaluation (1,y)) (r y):=by
    change Metric.ball x.val ε⊆Metric.ball ((1:S.Generated) •y.val) (r y)
    rw [one_smul]
    intro z hz
    have hzdist:dist z x.val<ε:=hz
    have he:=hbound y hy
    calc
      dist z y.val≤dist z x.val+dist x.val y.val:=dist_triangle _ _ _
      _<ε+r y/2:=add_lt_add hzdist hdist
      _≤r y:=by linarith
  refine ⟨h.recenteredChart S htFull (S.project (1,x)) ε,
    h.recenteredChart_center S htFull (S.project (1,x)) hsource hε,?_,fun _ _=>rfl⟩
  exact h.recenteredChart_target S htFull (S.project (1,x)) hball


/-- A true development chart restricts to any positive centered ball contained
in its actual target. -/
theorem nativePoincare_chart_restrict_ball {P:_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ}
    (S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (q:S.Development) (e:OpenPartialHomeomorph S.Development ℍ)
    (hq:q∈e.source) (he:EqOn e S.evaluation e.source) (ε:ℝ) (hε:0<ε)
    (hb:Metric.ball (S.evaluation q) ε⊆e.target) :
    ∃e':OpenPartialHomeomorph S.Development ℍ,q∈e'.source ∧
      e'.target=Metric.ball (S.evaluation q) ε ∧EqOn e' S.evaluation e'.source := by
  let e':=e.trans (OpenPartialHomeomorph.ofSet (Metric.ball (S.evaluation q) ε) Metric.isOpen_ball)
  refine ⟨e',?_,?_,?_⟩
  · change q∈e.source∩e ⁻¹'Metric.ball (S.evaluation q) ε
    exact ⟨hq,by change e q∈Metric.ball (S.evaluation q) ε;rw [he hq];exact Metric.mem_ball_self hε⟩
  · change Metric.ball (S.evaluation q) ε∩id ⁻¹'e.target=Metric.ball (S.evaluation q) ε
    exact inter_eq_left.mpr hb
  · intro y hy
    exact he hy.1


/-- The actual generated isometry transports a genuine centered ball chart to
its translated original copy. -/
theorem nativePoincare_chart_translate {P:_root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ}
    (S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (g:S.Generated) (q:S.Development)
    (e:OpenPartialHomeomorph S.Development ℍ) (hq:q∈e.source) (ε:ℝ)
    (ht:e.target=Metric.ball (S.evaluation q) ε) (he:EqOn e S.evaluation e.source) :
    ∃e':OpenPartialHomeomorph S.Development ℍ,g •q∈e'.source ∧
      e'.target=Metric.ball (S.evaluation (g •q)) ε ∧EqOn e' S.evaluation e'.source := by
  let L:=S.translationHomeomorph g⁻¹
  let R:=g.val.toHomeomorph
  let e':=(L.toOpenPartialHomeomorph.trans e).trans R.toOpenPartialHomeomorph
  have hL:L (g •q)=q:=inv_smul_smul g q
  refine ⟨e',?_,?_,?_⟩
  · change g •q∈(univ∩L ⁻¹'e.source)∩(e ∘ L) ⁻¹'univ
    exact ⟨⟨mem_univ _,by change L (g •q)∈e.source;rwa [hL]⟩,mem_univ _⟩
  · have heTarget:(L.toOpenPartialHomeomorph.trans e).target=e.target:=by
      change e.target∩e.symm ⁻¹'univ=e.target
      exact inter_univ _
    change ((L.toOpenPartialHomeomorph.trans e).trans R.toOpenPartialHomeomorph).target=_
    rw [OpenPartialHomeomorph.trans_target'']
    change R ''(univ∩(L.toOpenPartialHomeomorph.trans e).target)=_
    rw [univ_inter,heTarget,ht]
    change g.val ''Metric.ball (S.evaluation q) ε=Metric.ball (S.evaluation (g •q)) ε
    rw [g.val.image_ball,S.evaluation_smul]
    rfl
  · intro y hy
    have hLy:L y∈e.source:=hy.1.2
    change g.val (e (L y))=S.evaluation y
    rw [he hLy]
    change g •S.evaluation (g⁻¹ •y)=S.evaluation y
    rw [S.evaluation_smul,smul_inv_smul]

end LowDimensionalTopology.Geometry.Fuchsian


namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology

/-- The actual compact truncated core and actual cusp sections together provide
one true target-ball chart radius on the entire original development. -/
theorem cofiniteTangential_uniform_charts_of_cusp_sections {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (F:Fin n→Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hFI:∀i,θ i=0→F i • UpperHalfPlane.I=UpperHalfPlane.I)
    (hFp:∀i,θ i=0→(_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (F i)).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint)
    (Y:ℝ) (hY:0<Y)
    (hA6:(cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).FiniteFiberLocalTessellationCondition)
    (hCusp:∀i:Fin n,θ i=0→∃e:OpenPartialHomeomorph
        (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).Development ℍ,
      e.target={z:ℍ|Y<(F i •z).im} ∧
      EqOn e (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).evaluation e.source ∧
      ∀x:(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).Point,
        Y<(F i •x.val).im→
          (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).project (1,x)∈e.source) :
    let S:=cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
    ∃ε:ℝ,0<ε ∧∀q:S.Development,∃e:OpenPartialHomeomorph S.Development ℍ,
      q∈e.source ∧e.target=Metric.ball (S.evaluation q) ε ∧EqOn e S.evaluation e.source := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
  let S:=cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
  let K:Set ℍ:={z|z∈P.carrier ∧∀i:Fin n,θ i=0→(F i •z).im≤Y*Real.exp 1}
  have hK:IsCompact K:=cofiniteTangential_truncated_core_isCompact θ d hθ hd hb F hFI hFp (Y*Real.exp 1)
  obtain ⟨δ,hδ,hCore⟩:=nativePoincare_compact_subset_ball_charts S hA6 K hK (fun _ h=>h.1)
  let ε:=min δ 1
  have hε:0<ε:=lt_min hδ zero_lt_one
  have hOriginal:∀x:P.Point,∃e:OpenPartialHomeomorph S.Development ℍ,
      S.project (1,x)∈e.source ∧e.target=Metric.ball x.val ε ∧EqOn e S.evaluation e.source:=by
    intro x
    by_cases hx:x.val∈K
    · obtain ⟨e,he,ht,hm⟩:=hCore x hx
      have hball:Metric.ball (S.evaluation (S.project (1,x))) ε⊆e.target:=by
        rw [ht]
        change Metric.ball x.val ε⊆Metric.ball x.val δ
        exact Metric.ball_subset_ball (min_le_left _ _)
      exact nativePoincare_chart_restrict_ball S (S.project (1,x)) e he hm ε hε hball
    · have hnot:¬∀i:Fin n,θ i=0→(F i •x.val).im≤Y*Real.exp 1:=fun h=>hx ⟨x.property,h⟩
      push Not at hnot
      obtain ⟨i,hi,hHeight⟩:=hnot
      obtain ⟨e,ht,he,hsource⟩:=hCusp i hi
      have hYle:Y≤Y*Real.exp 1:=by
        have hh:1≤Real.exp 1:=Real.one_le_exp_iff.mpr (by norm_num)
        nlinarith
      have hxSource:S.project (1,x)∈e.source:=hsource x (hYle.trans_lt hHeight)
      have hball:Metric.ball (S.evaluation (S.project (1,x))) ε⊆e.target:=by
        rw [ht]
        intro z hz
        change dist z x.val<ε at hz
        change Y<(F i •z).im
        by_contra hn
        have hzY:(F i •z).im≤Y:=le_of_not_gt hn
        have hdist:dist (F i •x.val) (F i •z)<1:=by
          have heq:dist (F i •x.val) (F i •z)=dist x.val z:=
            (isometry_smul ℍ (F i)).dist_eq x.val z
          have hd0:dist x.val z<1:=by
            rw [dist_comm]
            exact lt_of_lt_of_le hz (min_le_right _ _)
          exact heq.trans_lt hd0
        have hprod:(F i •z).im*Real.exp (dist (F i •x.val) (F i •z))≤Y*Real.exp 1:=
          mul_le_mul hzY (Real.exp_le_exp.mpr hdist.le) (Real.exp_pos _).le hY.le
        have hu:=UpperHalfPlane.im_le_im_mul_exp_dist (F i •x.val) (F i •z)
        exact (not_lt_of_ge (hu.trans hprod)) hHeight
      exact nativePoincare_chart_restrict_ball S (S.project (1,x)) e hxSource he ε hε hball
  refine ⟨ε,hε,?_⟩
  intro q
  obtain ⟨⟨g,x⟩,rfl⟩:=Quotient.exists_rep q
  obtain ⟨e,he,ht,hm⟩:=hOriginal x
  have ht':e.target=Metric.ball (S.evaluation (S.project (1,x))) ε:=ht
  have hh:=nativePoincare_chart_translate S g (S.project (1,x)) e he ε ht' hm
  have htrans:g •S.project (1,x)=S.project (g,x):=by
    change S.project (g*1,x)=S.project (g,x)
    rw [mul_one]
  rw [htrans] at hh
  simpa only [_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.project] using hh

/--
The actual cusp sections and internally verified native local tessellation yield both
original Poincare conclusions; no discreteness or fundamental-domain premise is used.
-/
theorem cofiniteTangential_poincare_of_cusp_sections {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (F:Fin n→Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hFI:∀i,θ i=0→F i • UpperHalfPlane.I=UpperHalfPlane.I)
    (hFp:∀i,θ i=0→(_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (F i)).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint)
    (Y:ℝ) (hY:0<Y)
    (hA6:(cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).FiniteFiberLocalTessellationCondition)
    (hCusp:∀i:Fin n,θ i=0→∃e:OpenPartialHomeomorph
        (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).Development ℍ,
      e.target={z:ℍ|Y<(F i •z).im} ∧
      EqOn e (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).evaluation e.source ∧
      ∀x:(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).Point,
        Y<(F i •x.val).im→
          (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).project (1,x)∈e.source) :
    let S:=cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
    DiscreteTopology S.Generated ∧_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹'(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S:=cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
  obtain ⟨ε,hε,hCharts⟩:=cofiniteTangential_uniform_charts_of_cusp_sections θ d hθ hd hb ρ hρ hθρ
    F hFI hFp Y hY hA6 hCusp
  choose chart hmem htarget hmap using hCharts
  exact S.native_poincare_of_uniform_developing_charts hA6
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_interior_isOpen Q) (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_interior_isConnected Q)
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier Q) (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_countableSides Q)
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_geodesicSides Q) hε ⟨chart,hmem,htarget,hmap⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- Both actual contacts follow the positive original boundary orientation,
including a zero-angle ideal corner. No finite representative is required. -/
theorem cofiniteTangential_closed_corner_orientation {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n) :
    0 < OriginalOrientation.signedArea
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i)) 0 ∧
    0 < OriginalOrientation.signedArea
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))) 0 := by
  have hrad (r t a b : ℝ) :
      OriginalOrientation.signedArea
        (r • _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit a)
        (t • _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit b) 0 =
        r * t * Real.sin (b - a) := by
    simp only [OriginalOrientation.signedArea, zero_sub, map_sub,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.smul_re, Complex.smul_im, Complex.conj_re, Complex.conj_im,
      smul_eq_mul, _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_re, _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_im, Real.sin_sub]
    ring
  have hsin : 0 < Real.sin (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d) :=
    Real.sin_pos_of_pos_of_lt_pi (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_bounds (hθ i) hd).1
      (lt_trans (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_bounds (hθ i) hd).2 (by linarith only [Real.pi_pos]))
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_coordinate, _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot_coordinate,
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot_coordinate, _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_unit_next θ d hb i]
  constructor
  · rw [hrad, _root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle]
    rw [show _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i + _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d -
        _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i = _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d by ring]
    exact mul_pos (mul_pos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hd)
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_pos (hθ i) hd)) hsin
  · rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle_succ, hrad, _root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle]
    rw [show _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i + 2 * _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d -
        (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d i + _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d) =
        _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ i) d by ring]
    exact mul_pos (mul_pos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_pos (hθ i) hd)
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hd)) hsin

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual radial mirror, between the two centered zero-corner frames,
is the literal vertical-axis reflection. Only its actual endpoint transport is used. -/
theorem cofiniteTangential_zero_mirror_normalization {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i j : Fin n)
    (he : θ i = θ (finRotate n j)) (hi : θ i = 0)
    (r s : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hr : r • UpperHalfPlane.I = UpperHalfPlane.I) (hs : s • UpperHalfPlane.I = UpperHalfPlane.I)
    (hpr : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry r).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint)
    (hps : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd (finRotate n j)) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) (z : ℍ) :
    s • triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) z =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).reflection (r • z) := by
  obtain ⟨u, hu, hru, _hKr⟩ := cofiniteSL_centered_closed_rotation r hr
  obtain ⟨v, _hv, hsv, _hKs⟩ := cofiniteSL_centered_closed_rotation s hs
  let p := _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i
  let q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd (finRotate n j)
  let c : ℂ := Circle.exp
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (i.val + 1) + _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle θ d (j.val + 1))
  have htarget : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint : ℂ) = 1 := by
    apply OnePoint.coe_injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_toExtended]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty
  have hup : u * (p : ℂ) = 1 := by
    have h := hru p
    rw [hpr, htarget] at h
    exact h.symm
  have hvq : v * (q : ℂ) = 1 := by
    have h := hsv q
    rw [hps, htarget] at h
    exact h.symm
  have hpn : ‖(p : ℂ)‖ = 1 := (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_ideal_iff θ d hθ hd i).mpr hi
  have hU : u = conj (p : ℂ) := by
    apply mul_right_cancel₀ (norm_ne_zero_iff.mp (by rw [hpn]; norm_num))
    rw [hup, Complex.conj_mul', hpn]
    norm_num
  have hMpoint : c * conj (p : ℂ) = (q : ℂ) := by
    have h := congrArg (fun w : 𝕔𝔻 => (w : ℂ))
      (cofiniteTangentMirror_vertex_left θ d hθ hd hb i j he)
    change cofiniteTangentMirror θ d i j (p : ℂ) = (q : ℂ) at h
    rw [cofiniteTangentMirror, _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply] at h
    exact h
  have hvc : (v * c) * u = 1 := by
    rw [hU, mul_assoc, hMpoint, hvq]
  have hcoef : v * c = conj u := by
    apply mul_right_cancel₀ (norm_ne_zero_iff.mp (by rw [hu]; norm_num))
    rw [hvc, Complex.conj_mul', hu]
    norm_num
  have hfinite (a : Matrix.SpecialLinearGroup (Fin 2) ℝ) (b : ℂ)
      (h : ∀ w : 𝕔𝔻, ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry a).closedMap w : ℂ) = b * (w : ℂ)) (y : ℍ) :
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (a • y) : ℂ) = b * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y : ℂ) := by
    have hy := h (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes] at hy
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (a • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y)) : ℂ) = _ at hy
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] at hy
    exact hy
  have hMfinite (y : ℍ) :
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) y) : ℂ) =
        c * conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y : ℂ) := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (cofiniteTangentMirror θ d i j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y))) : ℂ) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap_coe,
      cofiniteTangentMirror, _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply]
    rfl
  have hRzero (y : ℍ) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).reflection y) : ℂ) =
      conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y : ℂ) := by
    have h := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_conjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] at h
    rw [congrFun _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisReflection_eq_reflection y] at h
    have h' := congrArg (fun w : ℍ => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w : ℂ)) h
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] at h'
    exact h'.symm
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
  apply Complex.UnitDisc.coe_injective
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (s • triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) z) : ℂ) =
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).reflection (r • z)) : ℂ)
  rw [hfinite s v hsv, hMfinite, hRzero, hfinite r u hru, map_mul]
  rw [← mul_assoc, hcoef]

/-- Each actual side element is the same positively signed nonzero translation
between the actual common-height frames, including an ideal singleton. -/
theorem cofiniteTangential_zero_pairing_normalization {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i j : Fin n)
    (he : θ i = θ (finRotate n j)) (hi : θ i = 0)
    (r s : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hr : r • UpperHalfPlane.I = UpperHalfPlane.I) (hs : s • UpperHalfPlane.I = UpperHalfPlane.I)
    (hpr : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry r).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint)
    (hps : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd (finRotate n j)) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) (z : ℍ) :
    s • cofiniteTangentPairingElement θ d hθ hd hb i j z =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2 * Real.sinh d) • (r • z) := by
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let L := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i
  have hout := (cofiniteTangential_zero_support_normalization θ d hθ hd hb i hi r hr hpr).2
  have hRef := L.reflection_realGL_conjugation (Matrix.SpecialLinearGroup.mapGL ℝ r) (r • z)
  change r • L.reflection (r⁻¹ • (r • z)) = _ at hRef
  rw [inv_smul_smul, hout] at hRef
  have htrans := congrFun (_root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_reflection_factor (2 * Real.sinh d) (-Real.sinh d)) (r • z)
  rw [show -Real.sinh d + 2 * Real.sinh d / 2 = 0 by ring] at htrans
  change s • triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) (L.reflection z) = _
  rw [cofiniteTangential_zero_mirror_normalization θ d hθ hd hb i j he hi r s hr hs hpr hps,
    hRef]
  exact htrans.symm

/-- One family of actual centered zero-corner frames gives the literal same
signed translation for every original paired side. No holonomy is postulated. -/
theorem cofiniteTangential_zero_pairing_frames {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (ρ : Equiv.Perm (Fin n))
    (hθρ : ∀ i, θ i = θ (finRotate n (ρ i))) :
    ∃ F : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ i, θ i = 0 →
      F i • UpperHalfPlane.I = UpperHalfPlane.I ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (F i)).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint ∧
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) ((finRotate n).symm i)).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ (F i)) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (Real.sinh d) ∧
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ (F i)) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (-Real.sinh d) ∧
      ∀ z : ℍ, F (finRotate n (ρ i)) • cofiniteTangentPairingElement θ d hθ hd hb i (ρ i) z =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2 * Real.sinh d) • (F i • z) := by
  have hex : ∀ i : Fin n, ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ, θ i = 0 →
      s • UpperHalfPlane.I = UpperHalfPlane.I ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint ∧
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) ((finRotate n).symm i)).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ s) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (Real.sinh d) ∧
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) i).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ s) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (-Real.sinh d) := by
    intro i
    by_cases hi : θ i = 0
    · obtain ⟨s, hs⟩ := cofiniteTangential_zero_support_frames θ d hθ hd hb i hi
      exact ⟨s, fun _ => hs⟩
    · exact ⟨1, fun h => (hi h).elim⟩
  choose F hF using hex
  refine ⟨F, ?_⟩
  intro i hi
  obtain ⟨hr, hpr, hin, hout⟩ := hF i hi
  have hnext : θ (finRotate n (ρ i)) = 0 := (hθρ i).symm.trans hi
  obtain ⟨hs, hps, _hin', _hout'⟩ := hF (finRotate n (ρ i)) hnext
  refine ⟨hr, hpr, hin, hout, ?_⟩
  intro z
  exact cofiniteTangential_zero_pairing_normalization θ d hθ hd hb i (ρ i) (hθρ i) hi
    (F i) (F (finRotate n (ρ i))) hr hs hpr hps z

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The same genuine deep strip has exactly its two original incident sides.
Its threshold also excludes every actual native vertex, so no side label is lost. -/
theorem cofiniteTangential_zero_deep_strip_sides {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n) (hi : θ i = 0)
    (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs : s • UpperHalfPlane.I = UpperHalfPlane.I)
    (hp : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry s).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ z : ℍ, Y < z.im →
      (s⁻¹ • z ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).carrier ↔
        -Real.sinh d ≤ z.re ∧ z.re ≤ Real.sinh d) ∧
      (s⁻¹ • z ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).interior ↔
        -Real.sinh d < z.re ∧ z.re < Real.sinh d) ∧
      ∀ j : Fin n, s⁻¹ • z ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) j →
        j = (finRotate n).symm i ∨ j = i := by
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P := _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
  have hQ : Q.IsConvex := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb
  have ha : ∀ j, Q.angle j < Real.pi := by
    intro j
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]
    exact (hθ j).2
  obtain ⟨Y₀, hY₀, hDeep⟩ := cofiniteTangential_zero_deep_strip θ d hθ hd hb i hi s hs hp
  have hFinite : ((fun x : ℍ => (s • x).im) '' _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q).Finite :=
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices_finite Q).image _
  obtain ⟨B, hB⟩ := hFinite.bddAbove
  refine ⟨max Y₀ (B + 1), lt_of_lt_of_le hY₀ (le_max_left _ _), ?_⟩
  intro z hz
  have hz₀ : Y₀ < z.im := lt_of_le_of_lt (le_max_left _ _) hz
  obtain ⟨hClosed, hOpen⟩ := hDeep z hz₀
  refine ⟨hClosed, hOpen, ?_⟩
  intro j hj
  have hNv : s⁻¹ • z ∉ _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q := by
    intro hv
    have hle := hB (Set.mem_image_of_mem (fun x : ℍ => (s • x).im) hv)
    rw [smul_inv_smul] at hle
    have hYB : B + 1 ≤ max Y₀ (B + 1) := le_max_right _ _
    linarith
  have hCarrier : s⁻¹ • z ∈ P.carrier :=
    P.side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q j) hj
  have hNotInside : s⁻¹ • z ∉ P.interior := by
    intro hx
    exact Set.disjoint_left.mp (P.interior_disjoint_side (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q j)) hx hj
  have hBounds := hClosed.mp hCarrier
  have hEnd : z.re = -Real.sinh d ∨ z.re = Real.sinh d := by
    by_cases hl : z.re = -Real.sinh d
    · exact Or.inl hl
    · right
      by_contra hr
      apply hNotInside
      apply hOpen.mpr
      exact ⟨lt_of_le_of_ne hBounds.1 (Ne.symm hl), lt_of_le_of_ne hBounds.2 hr⟩
  have hSupports := cofiniteTangential_zero_support_normalization θ d hθ hd hb i hi s hs hp
  have hPull (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
      (hx : z ∈ (L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ s)).carrier) :
      s⁻¹ • z ∈ L.carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier] at hx
    obtain ⟨y, hy, hzy⟩ := hx
    change s • y = z at hzy
    rw [← hzy, inv_smul_smul]
    exact hy
  rcases hEnd with hl | hr
  · have hLine : s⁻¹ • z ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier := by
      apply hPull
      rw [hSupports.2]
      exact hl
    have hSide : s⁻¹ • z ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i := by
      rw [cofiniteJordan_side_eq_carrier_inter_line Q hQ ha]
      exact ⟨hCarrier, hLine⟩
    right
    by_contra hji
    exact hNv (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q hji hj hSide)
  · have hLine : s⁻¹ • z ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q ((finRotate n).symm i)).carrier := by
      apply hPull
      rw [hSupports.1]
      exact hr
    have hSide : s⁻¹ • z ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q ((finRotate n).symm i) := by
      rw [cofiniteJordan_side_eq_carrier_inter_line Q hQ ha]
      exact ⟨hCarrier, hLine⟩
    left
    by_contra hji
    exact hNv (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q hji hj hSide)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The original endpoint-angle profile holds along the entire integer
corner orbit, preserving actual labels rather than their angle values. -/
theorem cofiniteTangential_zpow_corner_angle {n : ℕ} (θ : Fin n → ℝ)
    (ρ : Equiv.Perm (Fin n)) (hθρ : ∀ i, θ i = θ (finRotate n (ρ i))) (i : Fin n) (k : ℤ) :
    θ (((ρ.trans (finRotate n)) ^ k) i) = θ i := by
  let τ : Equiv.Perm (Fin n) := ρ.trans (finRotate n)
  have hstep (j : Fin n) : θ (τ j) = θ j := (hθρ j).symm
  have hall (k : ℤ) : ∀ j : Fin n, θ ((τ ^ k) j) = θ j := by
    induction k using Int.induction_on with
    | zero => intro j; simp
    | succ k ih =>
      intro j
      rw [zpow_add, zpow_one]
      change θ ((τ ^ (k : ℤ)) (τ j)) = θ j
      rw [ih, hstep]
    | pred k ih =>
      intro j
      rw [zpow_sub, zpow_one]
      change θ ((τ ^ (-(k : ℤ))) (τ⁻¹ j)) = θ j
      rw [ih]
      have h := hstep (τ⁻¹ j)
      simpa using h.symm
  exact hall k i

section ActualIdealWords
variable {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (ρ : Equiv.Perm (Fin n))
    (hθρ : ∀ i, θ i = θ (finRotate n (ρ i)))

/-- A single family chosen from the proved actual signed pairing frames. -/
def cofiniteTangentialIdealFrame : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  Classical.choose (cofiniteTangential_zero_pairing_frames θ d hθ hd hb ρ hθρ)

local notation "F₀" => cofiniteTangentialIdealFrame θ d hθ hd hb ρ hθρ
local notation "τ₀" => ρ.trans (finRotate n)
local notation "c₀" => 2 * Real.sinh d

theorem cofiniteTangentialIdealFrame_center (i : Fin n) (hi : θ i = 0) :
    F₀ i • UpperHalfPlane.I = UpperHalfPlane.I :=
  (Classical.choose_spec (cofiniteTangential_zero_pairing_frames θ d hθ hd hb ρ hθρ) i hi).1

theorem cofiniteTangentialIdealFrame_vertex (i : Fin n) (hi : θ i = 0) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry (F₀ i)).closedMap (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint :=
  (Classical.choose_spec (cofiniteTangential_zero_pairing_frames θ d hθ hd hb ρ hθρ) i hi).2.1

theorem cofiniteTangentialIdealFrame_transition (i : Fin n) (hi : θ i = 0) (z : ℍ) :
    F₀ (τ₀ i) • cofiniteTangentPairingElement θ d hθ hd hb i (ρ i) z =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL c₀ • (F₀ i • z) :=
  (Classical.choose_spec (cofiniteTangential_zero_pairing_frames θ d hθ hd hb ρ hθρ) i hi).2.2.2.2 z

/-- The literal original integer copy word in the genuine native isometry group. -/
def cofiniteTangentialIdealWord (i : Fin n) (k : ℤ) : ℍ ≃ᵢ ℍ :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F₀ i))⁻¹ * _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-(k : ℝ) * c₀)) *
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F₀ ((τ₀ ^ k) i))

local notation "W₀" => cofiniteTangentialIdealWord θ d hθ hd hb ρ hθρ

theorem cofiniteTangentialIdealWord_coordinate (i : Fin n) (k : ℤ) (z : ℍ) :
    F₀ i • W₀ i k z = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-(k : ℝ) * c₀) • (F₀ ((τ₀ ^ k) i) • z) := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F₀ i)) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F₀ i)).symm
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-(k : ℝ) * c₀)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F₀ ((τ₀ ^ k) i)) z))) = _
  rw [IsometryEquiv.apply_symm_apply]
  rfl

theorem cofiniteTangentialIdealWord_zero (i : Fin n) : W₀ i 0 = 1 := by
  apply IsometryEquiv.ext
  intro z
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F₀ i)).injective
  change F₀ i • W₀ i 0 z = F₀ i • z
  rw [cofiniteTangentialIdealWord_coordinate]
  simp only [zpow_zero, Equiv.Perm.coe_one, id_eq, Int.cast_zero, neg_zero, zero_mul]
  apply UpperHalfPlane.ext
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  simp

/-- Consecutive integer copies differ by the inverse of the actual original
side element at the current unchanged corner label. -/
theorem cofiniteTangentialIdealWord_step (i : Fin n) (hi : θ i = 0) (k : ℤ) :
    W₀ i (k + 1) = W₀ i k *
      (cofiniteTangentPairingElement θ d hθ hd hb ((τ₀ ^ k) i) (ρ ((τ₀ ^ k) i)))⁻¹ := by
  let j : Fin n := (τ₀ ^ k) i
  let a := cofiniteTangentPairingElement θ d hθ hd hb j (ρ j)
  have hj : θ j = 0 := (cofiniteTangential_zpow_corner_angle θ ρ hθρ i k).trans hi
  have hlabel : (τ₀ ^ (k + 1)) i = τ₀ j := by
    rw [show k + 1 = 1 + k by omega, zpow_add, zpow_one]
    rfl
  have hInv (z : ℍ) : F₀ j • (a⁻¹ z) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-c₀) • (F₀ (τ₀ j) • z) := by
    have h := cofiniteTangentialIdealFrame_transition θ d hθ hd hb ρ hθρ j hj (a⁻¹ z)
    change F₀ (τ₀ j) • a (a⁻¹ z) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL c₀ • (F₀ j • (a⁻¹ z)) at h
    rw [IsometryEquiv.apply_inv_self] at h
    have h' := congrArg (fun w : ℍ => (w : ℂ)) h
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe] at h'
    apply UpperHalfPlane.ext
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    push_cast at h' ⊢
    linear_combination -h'
  apply IsometryEquiv.ext
  intro z
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F₀ i)).injective
  change F₀ i • W₀ i (k + 1) z = F₀ i • W₀ i k (a⁻¹ z)
  rw [cofiniteTangentialIdealWord_coordinate, cofiniteTangentialIdealWord_coordinate, hlabel, hInv]
  apply UpperHalfPlane.ext
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  push_cast
  ring

/-- Every integer word belongs to the entire original raw side-generated
native group; this is derived from its actual pairing recursion. -/
theorem cofiniteTangentialIdealWord_mem (hρ : Function.Involutive ρ)
    (i : Fin n) (hi : θ i = 0) (k : ℤ) :
    W₀ i k ∈ (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).Generated := by
  let S := cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  have hA (j : Fin n) : cofiniteTangentPairingElement θ d hθ hd hb j (ρ j) ∈ S.Generated := by
    have h := (S.generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q j)).property
    change cofiniteTangentPairingElement θ d hθ hd hb
      ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q j))
      (ρ ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q j))) ∈ S.Generated at h
    simpa only [Equiv.symm_apply_apply] using h
  induction k using Int.induction_on with
  | zero =>
    rw [cofiniteTangentialIdealWord_zero]
    exact S.Generated.one_mem
  | succ k ih =>
    rw [cofiniteTangentialIdealWord_step θ d hθ hd hb ρ hθρ i hi]
    exact S.Generated.mul_mem ih (S.Generated.inv_mem (hA _))
  | pred k ih =>
    let m : ℤ := -(k : ℤ)
    let a := cofiniteTangentPairingElement θ d hθ hd hb ((τ₀ ^ (m - 1)) i) (ρ ((τ₀ ^ (m - 1)) i))
    have hstep := cofiniteTangentialIdealWord_step θ d hθ hd hb ρ hθρ i hi (m - 1)
    rw [sub_add_cancel] at hstep
    change W₀ i m = W₀ i (m - 1) * a⁻¹ at hstep
    have heq : W₀ i (m - 1) = W₀ i m * a := by
      calc
        W₀ i (m - 1) = (W₀ i (m - 1) * a⁻¹) * a := by group
        _ = W₀ i m * a := by rw [← hstep]
    change W₀ i (m - 1) ∈ S.Generated
    rw [heq]
    exact S.Generated.mul_mem ih (hA _)

theorem cofiniteTangentialIdealWord_injective (i : Fin n) (hi : θ i = 0) :
    Function.Injective (W₀ i) := by
  intro k l hkl
  have hfix (m : ℤ) : F₀ ((τ₀ ^ m) i) • UpperHalfPlane.I = UpperHalfPlane.I :=
    cofiniteTangentialIdealFrame_center θ d hθ hd hb ρ hθρ _
      ((cofiniteTangential_zpow_corner_angle θ ρ hθρ i m).trans hi)
  have heval (m : ℤ) : ((F₀ i • W₀ i m UpperHalfPlane.I : ℍ) : ℂ) =
      Complex.I + (-(m : ℝ) * c₀ : ℝ) := by
    rw [cofiniteTangentialIdealWord_coordinate, hfix, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    rfl
  have h := congrArg (fun f : ℍ ≃ᵢ ℍ => ((F₀ i • f UpperHalfPlane.I : ℍ) : ℂ).re) hkl
  rw [heval, heval] at h
  simp only [Complex.add_re, Complex.I_re, Complex.ofReal_re, zero_add] at h
  have hc : c₀ ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sinh_pos_iff.mpr hd)).ne'
  have hcast : (k : ℝ) = (l : ℝ) := neg_injective (mul_right_cancel₀ hc h)
  exact_mod_cast hcast

end ActualIdealWords
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

section ActualIdealCover
variable {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (ρ : Equiv.Perm (Fin n))
    (hθρ : ∀ i, θ i = θ (finRotate n (ρ i)))

local notation "F₀" => cofiniteTangentialIdealFrame θ d hθ hd hb ρ hθρ
local notation "τ₀" => ρ.trans (finRotate n)
local notation "c₀" => 2 * Real.sinh d
local notation "W₀" => cofiniteTangentialIdealWord θ d hθ hd hb ρ hθρ
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "P₀" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀

/-- Finitely many genuine zero-corner frames admit one actual deep height,
including the complete original incident-side exhaustion. -/
theorem cofiniteTangential_common_ideal_height :
    ∃ Y : ℝ, 0 < Y ∧ ∀ i, θ i = 0 → ∀ z : ℍ, Y < z.im →
      ((F₀ i)⁻¹ • z ∈ (P₀).carrier ↔ -Real.sinh d ≤ z.re ∧ z.re ≤ Real.sinh d) ∧
      ((F₀ i)⁻¹ • z ∈ (P₀).interior ↔ -Real.sinh d < z.re ∧ z.re < Real.sinh d) ∧
      ∀ j, (F₀ i)⁻¹ • z ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ j → j = (finRotate n).symm i ∨ j = i := by
  have hex : ∀ i : Fin n, ∃ Y : ℝ, 0 < Y ∧ (θ i = 0 → ∀ z : ℍ, Y < z.im →
      ((F₀ i)⁻¹ • z ∈ (P₀).carrier ↔ -Real.sinh d ≤ z.re ∧ z.re ≤ Real.sinh d) ∧
      ((F₀ i)⁻¹ • z ∈ (P₀).interior ↔ -Real.sinh d < z.re ∧ z.re < Real.sinh d) ∧
      ∀ j, (F₀ i)⁻¹ • z ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ j → j = (finRotate n).symm i ∨ j = i) := by
    intro i
    by_cases hi : θ i = 0
    · obtain ⟨Y, hY, hG⟩ := cofiniteTangential_zero_deep_strip_sides θ d hθ hd hb i hi (F₀ i)
        (cofiniteTangentialIdealFrame_center θ d hθ hd hb ρ hθρ i hi)
        (cofiniteTangentialIdealFrame_vertex θ d hθ hd hb ρ hθρ i hi)
      exact ⟨Y, hY, fun _ => hG⟩
    · exact ⟨1, zero_lt_one, fun h => (hi h).elim⟩
  choose Y hYpos hY using hex
  obtain ⟨B, hB⟩ := (Set.finite_range Y).bddAbove
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro i hi z hz
  apply hY i hi z
  exact lt_of_le_of_lt ((hB (Set.mem_range_self i)).trans (le_max_right _ _)) hz

/-- One fixed actual height chosen from the proved finite geometric family. -/
def cofiniteTangentialIdealHeight : ℝ :=
  Classical.choose (cofiniteTangential_common_ideal_height θ d hθ hd hb ρ hθρ)

local notation "H₀" => cofiniteTangentialIdealHeight θ d hθ hd hb ρ hθρ

theorem cofiniteTangentialIdealHeight_spec :
    0 < H₀ ∧ ∀ i, θ i = 0 → ∀ z : ℍ, H₀ < z.im →
      ((F₀ i)⁻¹ • z ∈ (P₀).carrier ↔ -Real.sinh d ≤ z.re ∧ z.re ≤ Real.sinh d) ∧
      ((F₀ i)⁻¹ • z ∈ (P₀).interior ↔ -Real.sinh d < z.re ∧ z.re < Real.sinh d) ∧
      ∀ j, (F₀ i)⁻¹ • z ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ j → j = (finRotate n).symm i ∨ j = i :=
  Classical.choose_spec (cofiniteTangential_common_ideal_height θ d hθ hd hb ρ hθρ)

/-- The closed high piece of an actual original native copy. -/
def cofiniteTangentialIdealClosedPiece (i : Fin n) (k : ℤ) : Set ℍ :=
  W₀ i k '' {z | z ∈ (P₀).carrier ∧ H₀ < (F₀ ((τ₀ ^ k) i) • z).im}

/-- The open high piece of the same actual original native copy. -/
def cofiniteTangentialIdealOpenPiece (i : Fin n) (k : ℤ) : Set ℍ :=
  W₀ i k '' {z | z ∈ (P₀).interior ∧ H₀ < (F₀ ((τ₀ ^ k) i) • z).im}

local notation "C₀" => cofiniteTangentialIdealClosedPiece θ d hθ hd hb ρ hθρ
local notation "O₀" => cofiniteTangentialIdealOpenPiece θ d hθ hd hb ρ hθρ

/-- The genuine integer copy pieces have their literal closed and open
translated strip coordinates in the original base frame. -/
theorem cofiniteTangentialIdealPieces_iff (i : Fin n) (hi : θ i = 0) (k : ℤ) (x : ℍ) :
    (x ∈ C₀ i k ↔ H₀ < (F₀ i • x).im ∧
      -Real.sinh d - (k : ℝ) * c₀ ≤ (F₀ i • x).re ∧
      (F₀ i • x).re ≤ Real.sinh d - (k : ℝ) * c₀) ∧
    (x ∈ O₀ i k ↔ H₀ < (F₀ i • x).im ∧
      -Real.sinh d - (k : ℝ) * c₀ < (F₀ i • x).re ∧
      (F₀ i • x).re < Real.sinh d - (k : ℝ) * c₀) := by
  let j : Fin n := (τ₀ ^ k) i
  let y : ℍ := (W₀ i k)⁻¹ x
  let g : ℍ := F₀ j • y
  have hj : θ j = 0 := (cofiniteTangential_zpow_corner_angle θ ρ hθρ i k).trans hi
  have hCoord := cofiniteTangentialIdealWord_coordinate θ d hθ hd hb ρ hθρ i k y
  change F₀ i • W₀ i k ((W₀ i k)⁻¹ x) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-(k : ℝ) * c₀) • g at hCoord
  rw [IsometryEquiv.apply_inv_self] at hCoord
  have hIm : g.im = (F₀ i • x).im := by
    have h := congrArg UpperHalfPlane.im hCoord
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_im] at h
    exact h.symm
  have hRe : g.re = (F₀ i • x).re + (k : ℝ) * c₀ := by
    have h := congrArg (fun z : ℍ => (z : ℂ).re) hCoord
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe] at h
    simp only [Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re] at h
    linarith
  have hG (hH : H₀ < g.im) :
      (y ∈ (P₀).carrier ↔ -Real.sinh d ≤ g.re ∧ g.re ≤ Real.sinh d) ∧
      (y ∈ (P₀).interior ↔ -Real.sinh d < g.re ∧ g.re < Real.sinh d) := by
    have h := (cofiniteTangentialIdealHeight_spec θ d hθ hd hb ρ hθρ).2 j hj g hH
    refine ⟨?_, ?_⟩
    · simpa only [g, inv_smul_smul] using h.1
    · simpa only [g, inv_smul_smul] using h.2.1
  have hImage (A : Set ℍ) : x ∈ W₀ i k '' A ↔ y ∈ A := by
    constructor
    · rintro ⟨z, hz, hzx⟩
      change (W₀ i k)⁻¹ x ∈ A
      rw [← hzx, IsometryEquiv.inv_apply_self]
      exact hz
    · intro hy
      exact ⟨y, hy, IsometryEquiv.apply_inv_self (W₀ i k) x⟩
  constructor
  · change x ∈ W₀ i k '' {z | z ∈ (P₀).carrier ∧ H₀ < (F₀ j • z).im} ↔ _
    rw [hImage]
    change (y ∈ (P₀).carrier ∧ H₀ < g.im) ↔ _
    constructor
    · rintro ⟨hC, hH⟩
      have hb := (hG hH).1.mp hC
      rw [hRe] at hb
      exact ⟨by rwa [← hIm], by linarith [hb.1], by linarith [hb.2]⟩
    · rintro ⟨hH, hl, hr⟩
      have hY : H₀ < g.im := by rwa [hIm]
      refine ⟨(hG hY).1.mpr ?_, hY⟩
      rw [hRe]
      constructor <;> linarith
  · change x ∈ W₀ i k '' {z | z ∈ (P₀).interior ∧ H₀ < (F₀ j • z).im} ↔ _
    rw [hImage]
    change (y ∈ (P₀).interior ∧ H₀ < g.im) ↔ _
    constructor
    · rintro ⟨hC, hH⟩
      have hb := (hG hH).2.mp hC
      rw [hRe] at hb
      exact ⟨by rwa [← hIm], by linarith [hb.1], by linarith [hb.2]⟩
    · rintro ⟨hH, hl, hr⟩
      have hY : H₀ < g.im := by rwa [hIm]
      refine ⟨(hG hY).2.mpr ?_, hY⟩
      rw [hRe]
      constructor <;> linarith

/-- All actual closed integer copy pieces cover the entire genuine native
high horoball in the original base frame. -/
theorem cofiniteTangentialIdealClosedPiece_cover (i : Fin n) (hi : θ i = 0) :
    (⋃ k : ℤ, C₀ i k) = {x : ℍ | H₀ < (F₀ i • x).im} := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    exact ((cofiniteTangentialIdealPieces_iff θ d hθ hd hb ρ hθρ i hi k x).1.mp hk).1
  · intro hx
    have hc : 0 < c₀ := mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sinh_pos_iff.mpr hd)
    let a : ℝ := (F₀ i • x).re
    let q : ℤ := ⌊(a + Real.sinh d) / c₀⌋
    have hlo : (q : ℝ) * c₀ ≤ a + Real.sinh d :=
      (le_div_iff₀ hc).mp (Int.floor_le _)
    have hhi : a + Real.sinh d < ((q : ℝ) + 1) * c₀ :=
      (div_lt_iff₀ hc).mp (Int.lt_floor_add_one _)
    apply Set.mem_iUnion.mpr
    refine ⟨-q, (cofiniteTangentialIdealPieces_iff θ d hθ hd hb ρ hθρ i hi (-q) x).1.mpr ?_⟩
    refine ⟨hx, ?_, ?_⟩
    all_goals
      dsimp only [a] at hlo hhi
      push_cast
      nlinarith only [hlo, hhi]

/-- Distinct actual open integer copy pieces are disjoint, by their literal
signed consecutive strip coordinates and the integer unit gap. -/
theorem cofiniteTangentialIdealOpenPiece_pairwiseDisjoint (i : Fin n) (hi : θ i = 0) :
    Set.PairwiseDisjoint (Set.univ : Set ℤ) (O₀ i) := by
  intro k _hk l _hl hkl
  apply Set.disjoint_left.mpr
  intro x hxk hxl
  have hk := (cofiniteTangentialIdealPieces_iff θ d hθ hd hb ρ hθρ i hi k x).2.mp hxk
  have hl := (cofiniteTangentialIdealPieces_iff θ d hθ hd hb ρ hθρ i hi l x).2.mp hxl
  have hc : 0 < c₀ := mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sinh_pos_iff.mpr hd)
  rcases lt_or_gt_of_ne hkl with hkl | hlk
  · have hInt : k + 1 ≤ l := by omega
    have hgap : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hInt
    have hgapc := mul_le_mul_of_nonneg_right hgap hc.le
    nlinarith only [hk.2.1, hl.2.2, hgapc]
  · have hInt : l + 1 ≤ k := by omega
    have hgap : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hInt
    have hgapc := mul_le_mul_of_nonneg_right hgap hc.le
    nlinarith only [hl.2.1, hk.2.2, hgapc]

end ActualIdealCover
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
  Filter
  Topology

section ActualIdealSection
variable {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (ρ : Equiv.Perm (Fin n))
    (hρ : Function.Involutive ρ) (hθρ : ∀ i, θ i = θ (finRotate n (ρ i)))

local notation "F₀" => cofiniteTangentialIdealFrame θ d hθ hd hb ρ hθρ
local notation "τ₀" => ρ.trans (finRotate n)
local notation "c₀" => 2 * Real.sinh d
local notation "W₀" => cofiniteTangentialIdealWord θ d hθ hd hb ρ hθρ
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "P₀" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀
local notation "S₀" => cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
local notation "H₀" => cofiniteTangentialIdealHeight θ d hθ hd hb ρ hθρ
local notation "C₀" => cofiniteTangentialIdealClosedPiece θ d hθ hd hb ρ hθρ

/-- An original high integer copy, retaining its actual full generated-group
coordinate and actual original polygon point. -/
def cofiniteTangentialIdealCopy (i : Fin n) (hi : θ i = 0) (k : ℤ)
    (x : ℍ) (hx : x ∈ C₀ i k) : (S₀).Copy :=
  (⟨W₀ i k, cofiniteTangentialIdealWord_mem θ d hθ hd hb ρ hθρ hρ i hi k⟩,
    ⟨(W₀ i k)⁻¹ x, by
      obtain ⟨y, hy, rfl⟩ := hx
      simpa only [IsometryEquiv.inv_apply_self] using hy.1⟩)

local notation "K₀" => cofiniteTangentialIdealCopy θ d hθ hd hb ρ hρ hθρ

theorem cofiniteTangentialIdealCopy_evaluation (i : Fin n) (hi : θ i = 0) (k : ℤ)
    (x : ℍ) (hx : x ∈ C₀ i k) : (S₀).copyEvaluation (K₀ i hi k x hx) = x :=
  IsometryEquiv.apply_inv_self (W₀ i k) x

/-- Shared closed-strip boundaries are genuine original outgoing sides,
so consecutive actual copies have precisely the original side identification. -/
theorem cofiniteTangentialIdealCopy_adjacent (i : Fin n) (hi : θ i = 0) (k : ℤ)
    (x : ℍ) (hx : x ∈ C₀ i k) (hx' : x ∈ C₀ i (k + 1)) :
    (S₀).Step (K₀ i hi k x hx) (K₀ i hi (k + 1) x hx') := by
  let j : Fin n := (τ₀ ^ k) i
  let y : ℍ := (W₀ i k)⁻¹ x
  let a := cofiniteTangentPairingElement θ d hθ hd hb j (ρ j)
  let side := _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ j
  have hj : θ j = 0 := (cofiniteTangential_zpow_corner_angle θ ρ hθρ i k).trans hi
  have hK := (cofiniteTangentialIdealPieces_iff θ d hθ hd hb ρ hθρ i hi k x).1.mp hx
  have hK' := (cofiniteTangentialIdealPieces_iff θ d hθ hd hb ρ hθρ i hi (k + 1) x).1.mp hx'
  have hRe : (F₀ j • y).re = -Real.sinh d := by
    have hCoord := cofiniteTangentialIdealWord_coordinate θ d hθ hd hb ρ hθρ i k y
    change F₀ i • W₀ i k ((W₀ i k)⁻¹ x) = _ at hCoord
    rw [IsometryEquiv.apply_inv_self] at hCoord
    have h := congrArg (fun z : ℍ => (z : ℂ).re) hCoord
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe] at h
    simp only [Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re] at h
    push_cast at hK'
    nlinarith only [hK.2.1, hK'.2.2, h]
  have hC : y ∈ (P₀).carrier := (K₀ i hi k x hx).2.property
  have hL : y ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q₀ j).carrier := by
    have hs := (Classical.choose_spec
      (cofiniteTangential_zero_pairing_frames θ d hθ hd hb ρ hθρ) j hj).2.2.2.1
    change (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q₀ j).realGLMap
      (Matrix.SpecialLinearGroup.mapGL ℝ (F₀ j)) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (-Real.sinh d) at hs
    have hmem : F₀ j • y ∈ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q₀ j).realGLMap
        (Matrix.SpecialLinearGroup.mapGL ℝ (F₀ j))).carrier := by
      rw [hs]
      exact hRe
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier] at hmem
    obtain ⟨z, hz, heq⟩ := hmem
    have heq' : F₀ j • z = F₀ j • y := heq
    exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F₀ j)).injective heq') ▸ hz
  have hside : y ∈ side.val := by
    change y ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ j
    rw [cofiniteJordan_side_eq_carrier_inter_line Q₀
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb)
      (fun l => by rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]; exact (hθ l).2)]
    exact ⟨hC, hL⟩
  have ha : ((S₀).generator side).val = a := by
    change cofiniteTangentPairingElement θ d hθ hd hb
      ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ j))
      (ρ ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀).symm (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ j))) = a
    simp only [Equiv.symm_apply_apply]
    rfl
  have hword : W₀ i (k + 1) = W₀ i k * a⁻¹ :=
    cofiniteTangentialIdealWord_step θ d hθ hd hb ρ hθρ i hi k
  apply Or.inr
  refine ⟨side, hside, ?_, ?_⟩
  · change (W₀ i (k + 1))⁻¹ x = ((S₀).generator side).val y
    rw [ha, hword, mul_inv_rev]
    rfl
  · apply Subtype.ext
    change W₀ i k = W₀ i (k + 1) * ((S₀).generator side).val
    rw [ha, hword]
    group

/-- Every possible overlap of actual high closed pieces is generated by the
literal original side gluing; no global packing assumption is used. -/
theorem cofiniteTangentialIdealCopy_project_eq (i : Fin n) (hi : θ i = 0)
    (k l : ℤ) (x : ℍ) (hk : x ∈ C₀ i k) (hl : x ∈ C₀ i l) :
    (S₀).project (K₀ i hi k x hk) = (S₀).project (K₀ i hi l x hl) := by
  have hbound : k = l ∨ l = k + 1 ∨ k = l + 1 := by
    have hK := (cofiniteTangentialIdealPieces_iff θ d hθ hd hb ρ hθρ i hi k x).1.mp hk
    have hL := (cofiniteTangentialIdealPieces_iff θ d hθ hd hb ρ hθρ i hi l x).1.mp hl
    have hc : 0 < c₀ := mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sinh_pos_iff.mpr hd)
    by_contra hn
    have hgap : k + 2 ≤ l ∨ l + 2 ≤ k := by omega
    rcases hgap with hgap | hgap
    · have hr : (k : ℝ) + 2 ≤ (l : ℝ) := by exact_mod_cast hgap
      have hm := mul_le_mul_of_nonneg_right hr hc.le
      nlinarith only [hK.2.1, hL.2.2, hm, hc]
    · have hr : (l : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgap
      have hm := mul_le_mul_of_nonneg_right hr hc.le
      nlinarith only [hL.2.1, hK.2.2, hm, hc]
  rcases hbound with rfl | rfl | rfl
  · rfl
  · exact (S₀).project_eq_iff _ _ |>.mpr
      (Relation.EqvGen.rel _ _ (cofiniteTangentialIdealCopy_adjacent θ d hθ hd hb ρ hρ hθρ i hi k x hk hl))
  · exact ((S₀).project_eq_iff _ _ |>.mpr
      (Relation.EqvGen.rel _ _ (cofiniteTangentialIdealCopy_adjacent θ d hθ hd hb ρ hρ hθρ i hi l x hl hk))).symm

/-- The actual high horoball is an open subset of the original native plane. -/
def cofiniteTangentialIdealHoroball (i : Fin n) : Set ℍ :=
  {x | H₀ < (F₀ i • x).im}

local notation "B₀" => cofiniteTangentialIdealHoroball θ d hθ hd hb ρ hθρ

theorem cofiniteTangentialIdealHoroball_isOpen (i : Fin n) : IsOpen (B₀ i) := by
  exact isOpen_lt continuous_const
    (UpperHalfPlane.continuous_im.comp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F₀ i)).continuous)

/-- In the genuine high horoball, the actual closed copy pieces form a
locally finite closed cover, including their original common boundaries. -/
theorem cofiniteTangentialIdealClosedPiece_closed_cover (i : Fin n) (hi : θ i = 0) :
    (∀ k : ℤ, IsClosed {x : B₀ i | x.val ∈ C₀ i k}) ∧
    (⋃ k : ℤ, {x : B₀ i | x.val ∈ C₀ i k}) = Set.univ ∧
    LocallyFinite (fun k : ℤ => {x : B₀ i | x.val ∈ C₀ i k}) := by
  have hcont : Continuous (fun x : B₀ i => (F₀ i • x.val).re) :=
    UpperHalfPlane.continuous_re.comp
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F₀ i)).continuous.comp continuous_subtype_val)
  have hIcc (k : ℤ) : {x : B₀ i | x.val ∈ C₀ i k} =
      (fun x : B₀ i => (F₀ i • x.val).re) ⁻¹'
        Set.Icc (-Real.sinh d - (k : ℝ) * c₀) (Real.sinh d - (k : ℝ) * c₀) := by
    ext x
    exact (cofiniteTangentialIdealPieces_iff θ d hθ hd hb ρ hθρ i hi k x.val).1.trans
      (and_iff_right x.property)
  refine ⟨fun k => by rw [hIcc]; exact isClosed_Icc.preimage hcont, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x.val ∈ ⋃ k : ℤ, C₀ i k := by
      rw [cofiniteTangentialIdealClosedPiece_cover θ d hθ hd hb ρ hθρ i hi]
      exact x.property
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  · intro x
    let a : ℝ := (F₀ i • x.val).re
    let lo : ℤ := ⌊(-Real.sinh d - a - 1) / c₀⌋
    let hi' : ℤ := ⌈(Real.sinh d - a + 1) / c₀⌉
    let U : Set (B₀ i) := (fun y : B₀ i => (F₀ i • y.val).re) ⁻¹' Set.Ioo (a - 1) (a + 1)
    have hU : U ∈ 𝓝 x := hcont.continuousAt
      (Ioo_mem_nhds (by dsimp only [a]; linarith) (by dsimp only [a]; linarith))
    refine ⟨U, hU, (Set.finite_Icc lo hi').subset ?_⟩
    rintro k ⟨y, hy, hyU⟩
    have hk := (cofiniteTangentialIdealPieces_iff θ d hθ hd hb ρ hθρ i hi k y.val).1.mp hy
    have hyU' : a - 1 < (F₀ i • y.val).re ∧ (F₀ i • y.val).re < a + 1 := hyU
    have hc : 0 < c₀ := mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sinh_pos_iff.mpr hd)
    have hlow : (lo : ℝ) ≤ (k : ℝ) := by
      apply (Int.floor_le _).trans
      apply (div_le_iff₀ hc).mpr
      linarith only [hk.2.1, hyU'.2]
    have hupp : (k : ℝ) ≤ (hi' : ℝ) := by
      apply le_trans _ (Int.le_ceil _)
      apply (le_div_iff₀ hc).mpr
      linarith only [hk.2.2, hyU'.1]
    constructor
    · exact_mod_cast hlow
    · exact_mod_cast hupp

/-- A copy label exists for every point of the genuine original high horoball. -/
theorem cofiniteTangentialIdealCopy_exists (i : Fin n) (hi : θ i = 0) (x : B₀ i) :
    ∃ k : ℤ, x.val ∈ C₀ i k := by
  apply Set.mem_iUnion.mp
  rw [cofiniteTangentialIdealClosedPiece_cover θ d hθ hd hb ρ hθρ i hi]
  exact x.property

/-- The developed cusp section is selected from the proved actual original
integer copies; agreement on every overlap is proved separately. -/
def cofiniteTangentialIdealSection (i : Fin n) (hi : θ i = 0) (x : B₀ i) : (S₀).Development :=
  (S₀).project (K₀ i hi
    (Classical.choose (cofiniteTangentialIdealCopy_exists θ d hθ hd hb ρ hθρ i hi x))
    x.val (Classical.choose_spec (cofiniteTangentialIdealCopy_exists θ d hθ hd hb ρ hθρ i hi x)))

local notation "σ₀" => cofiniteTangentialIdealSection θ d hθ hd hb ρ hρ hθρ

/-- The section agrees with every containing original copy, including at an
actual common side. This removes all dependence on the selected label. -/
theorem cofiniteTangentialIdealSection_eq_copy (i : Fin n) (hi : θ i = 0) (x : B₀ i)
    (k : ℤ) (hx : x.val ∈ C₀ i k) :
    σ₀ i hi x = (S₀).project (K₀ i hi k x.val hx) :=
  cofiniteTangentialIdealCopy_project_eq θ d hθ hd hb ρ hρ hθρ i hi _ _ x.val _ hx

theorem cofiniteTangentialIdealSection_evaluation (i : Fin n) (hi : θ i = 0) (x : B₀ i) :
    (S₀).evaluation (σ₀ i hi x) = x.val := by
  obtain ⟨k, hk⟩ := cofiniteTangentialIdealCopy_exists θ d hθ hd hb ρ hθρ i hi x
  rw [cofiniteTangentialIdealSection_eq_copy θ d hθ hd hb ρ hρ hθρ i hi x k hk]
  exact cofiniteTangentialIdealCopy_evaluation θ d hθ hd hb ρ hρ hθρ i hi k x.val hk

/-- Actual fixed-copy projection maps paste continuously along the locally
finite original closed strip cover; no global injectivity is assumed. -/
theorem cofiniteTangentialIdealSection_continuous (i : Fin n) (hi : θ i = 0) :
    Continuous (σ₀ i hi) := by
  obtain ⟨hclosed, hcover, hLF⟩ :=
    cofiniteTangentialIdealClosedPiece_closed_cover θ d hθ hd hb ρ hθρ i hi
  apply hLF.continuous hcover hclosed
  intro k
  rw [continuousOn_iff_continuous_domRestrict]
  have hpoint : Continuous (fun x : {x : B₀ i // x.val ∈ C₀ i k} =>
      (K₀ i hi k x.val.val x.property).2) := by
    apply Continuous.subtype_mk
    exact ((W₀ i k)⁻¹).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)
  let : TopologicalSpace (S₀).Generated := ⊥
  have hcopy : Continuous (fun x : {x : B₀ i // x.val ∈ C₀ i k} =>
      K₀ i hi k x.val.val x.property) := continuous_const.prodMk hpoint
  apply ((S₀).continuous_project.comp hcopy).congr
  intro x
  exact (cofiniteTangentialIdealSection_eq_copy θ d hθ hd hb ρ hρ hθρ i hi x.val k x.property).symm

/-- The continuous cusp section contains the original identity copy itself
at every genuine high point of the original polygon. -/
theorem cofiniteTangentialIdealSection_identity_copy (i : Fin n) (hi : θ i = 0)
    (x : (P₀).Point) (hx : H₀ < (F₀ i • x.val).im) :
    σ₀ i hi ⟨x.val, hx⟩ = (S₀).project (1, x) := by
  have hC : x.val ∈ C₀ i 0 := by
    refine ⟨x.val, ⟨x.property, ?_⟩, ?_⟩
    · simpa only [zpow_zero, Equiv.Perm.coe_one, id_eq] using hx
    · rw [cofiniteTangentialIdealWord_zero]
      rfl
  rw [cofiniteTangentialIdealSection_eq_copy θ d hθ hd hb ρ hρ hθρ i hi ⟨x.val, hx⟩ 0 hC]
  apply congrArg (S₀).project
  apply Prod.ext
  · apply Subtype.ext
    exact cofiniteTangentialIdealWord_zero θ d hθ hd hb ρ hθρ i
  · apply Subtype.ext
    change (W₀ i 0)⁻¹ x.val = x.val
    rw [cofiniteTangentialIdealWord_zero]
    rfl

/--
With the already geometrically established local tessellation, the actual cusp section
is an open embedding of the entire genuine high horoball.
-/
theorem cofiniteTangentialIdealSection_isOpenEmbedding
    (hA6 : (S₀).FiniteFiberLocalTessellationCondition) (i : Fin n) (hi : θ i = 0) :
    IsOpenEmbedding (σ₀ i hi) := by
  let : IsIsometricSMul (S₀).Generated ℍ := ⟨fun g => g.val.isometry⟩
  have hcomp : (S₀).evaluation ∘ σ₀ i hi = (Subtype.val : B₀ i → ℍ) :=
    funext (cofiniteTangentialIdealSection_evaluation θ d hθ hd hb ρ hρ hθρ i hi)
  apply (hA6.isLocalHomeomorph_evaluation (S₀)).isOpenEmbedding_of_comp
  · rw [hcomp]
    exact (cofiniteTangentialIdealHoroball_isOpen θ d hθ hd hb ρ hθρ i).isOpenEmbedding_subtypeVal
  · exact cofiniteTangentialIdealSection_continuous θ d hθ hd hb ρ hρ hθρ i hi

/-- The original high cusp has an actual open development chart whose
forward map is the original evaluation and whose source contains every high
point of the original identity copy. -/
theorem cofiniteTangentialIdeal_openPartialHomeomorph
    (hA6 : (S₀).FiniteFiberLocalTessellationCondition) (i : Fin n) (hi : θ i = 0) :
    ∃ e : OpenPartialHomeomorph (S₀).Development ℍ,
      e.target = B₀ i ∧ EqOn e (S₀).evaluation e.source ∧
      ∀ x : (P₀).Point, H₀ < (F₀ i • x.val).im → (S₀).project (1, x) ∈ e.source := by
  let : IsIsometricSMul (S₀).Generated ℍ := ⟨fun g => g.val.isometry⟩
  have hσ := cofiniteTangentialIdealSection_isOpenEmbedding θ d hθ hd hb ρ hρ hθρ hA6 i hi
  have hEval := hA6.isLocalHomeomorph_evaluation (S₀)
  have hinj : Set.InjOn (S₀).evaluation (Set.range (σ₀ i hi)) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    have hval : x.val = y.val := by
      simpa only [cofiniteTangentialIdealSection_evaluation] using hxy
    exact congrArg (σ₀ i hi) (Subtype.ext hval)
  let e : OpenPartialHomeomorph (S₀).Development ℍ :=
    OpenPartialHomeomorph.ofContinuousOpen
      (hinj.toPartialEquiv (S₀).evaluation (Set.range (σ₀ i hi)))
      hEval.continuous.continuousOn hEval.isOpenMap hσ.isOpen_range
  refine ⟨e, ?_, fun _ _ => rfl, ?_⟩
  · change (S₀).evaluation '' Set.range (σ₀ i hi) = B₀ i
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      rw [cofiniteTangentialIdealSection_evaluation]
      exact y.property
    · intro hx
      refine ⟨σ₀ i hi ⟨x, hx⟩, Set.mem_range_self _, ?_⟩
      exact cofiniteTangentialIdealSection_evaluation θ d hθ hd hb ρ hρ hθρ i hi ⟨x, hx⟩
  · intro x hx
    change (S₀).project (1, x) ∈ Set.range (σ₀ i hi)
    exact ⟨⟨x.val, hx⟩, cofiniteTangentialIdealSection_identity_copy θ d hθ hd hb ρ hρ hθρ i hi x hx⟩

end ActualIdealSection
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
  Topology

/-- The actual finite-angle fans and actual infinite cusp strips give the
original discrete native group and its literal fundamental polygon. -/
theorem cofiniteTangential_mixed_poincare {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,0<θ i→∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N) :
    let S:=cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
    DiscreteTopology S.Generated ∧_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹'(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior) := by
  have hA6:=cofiniteTangential_mixed_local_tessellation θ d hθ hd hb ρ hρ hθρ hPeriod
  apply cofiniteTangential_poincare_of_cusp_sections θ d hθ hd hb ρ hρ hθρ
    (cofiniteTangentialIdealFrame θ d hθ hd hb ρ hθρ)
    (cofiniteTangentialIdealFrame_center θ d hθ hd hb ρ hθρ)
    (cofiniteTangentialIdealFrame_vertex θ d hθ hd hb ρ hθρ)
    (cofiniteTangentialIdealHeight θ d hθ hd hb ρ hθρ)
    (cofiniteTangentialIdealHeight_spec θ d hθ hd hb ρ hθρ).1 hA6
  exact cofiniteTangentialIdeal_openPartialHomeomorph θ d hθ hd hb ρ hρ hθρ hA6

/-- Every allowed finite/cusped prescribed signature has the genuine
discrete native pairing group and literal polygonal fundamental domain. -/
theorem cofiniteConstruction_mixed_poincare (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,m=0∨2≤m) (hlast:last=0∨2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i=>(cofiniteConstructionAngles g ms last)[i]) d=Real.pi) :
    let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=
      fun i=>(cofiniteConstructionAngles g ms last)[i]
    let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last
      hms hlast hdef _ (List.getElem_mem i.isLt)
    let S:=cofiniteTangentialSidePairing θ d hθ hd hb (cofiniteConstructionPairing g ms last)
      (cofiniteConstructionPairing_involutive g ms last)
      (cofiniteConstructionPairing_angle_profile g ms last)
    DiscreteTopology S.Generated ∧_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹'(_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior) := by
  dsimp only
  apply cofiniteTangential_mixed_poincare
  intro i hi
  exact cofiniteConstruction_mixed_angular_periods g ms last hms hlast hdef i hi

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

section ProjectiveModel
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))

/-- Every generator of the actual common-incircle group is positively conformal. -/
theorem cofiniteMixedTangentialGenerated_conformal :
    (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).Generated≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨s,rfl⟩
  obtain ⟨i,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb)).surjective s
  rw [cofiniteTangentialJordanSidePairing_element_index]
  exact cofiniteTangentPairingElement_conformal θ d hθ hd hb i (ρ i)

/-- The genuine projective boundary representation of the actual native group. -/
def cofiniteMixedTangentialToMobius :
    (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).Generated→*
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  nativeConformalSubgroupMobiusHom _
    (cofiniteMixedTangentialGenerated_conformal θ d hθ hd hb ρ hρ hθρ)

/-- The entire faithful image of the original generated group. -/
def cofiniteMixedTangentialMobiusGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  (cofiniteMixedTangentialToMobius θ d hθ hd hb ρ hρ hθρ).range

/-- The native and projective groups differ only in their subtype labels. -/
def cofiniteMixedTangentialGroupEquiv :
    (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).Generated≃*
      cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ :=
  MulEquiv.ofBijective
    (cofiniteMixedTangentialToMobius θ d hθ hd hb ρ hρ hθρ).rangeRestrict
    ⟨fun _a _b h=>(nativeConformalSubgroupMobiusHom_isometry _
      (cofiniteMixedTangentialGenerated_conformal θ d hθ hd hb ρ hρ hθρ)).injective
        (congrArg Subtype.val h),
      (cofiniteMixedTangentialToMobius θ d hθ hd hb ρ hρ hθρ).rangeRestrict_surjective⟩

variable (hPeriod:∀i:Fin n,0<θ i→∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
include hPeriod

/-- The actual polygon construction supplies the genuine projective Fuchsian data. -/
theorem cofiniteMixedTangentialHalfPlaneData :
    HalfPlaneFuchsianGroup (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ) := by
  let : DiscreteTopology
      (cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).Generated:=
    (cofiniteTangential_mixed_poincare θ d hθ hd hb ρ hρ hθρ hPeriod).1
  exact nativeConformalSubgroup_halfPlaneData _
    (cofiniteMixedTangentialGenerated_conformal θ d hθ hd hb ρ hρ hθρ)

/-- The equivalence intertwines the original action at every actual half-plane point. -/
theorem cofiniteMixedTangentialGroupEquiv_action
    (g:(cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ).Generated) (z:ℍ) :
    letI:=(cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod).nativeAction
    cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ g • z=g.val z := by
  let originalAction:=
    (cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod).nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [←(cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod).nativeAction_boundary]
  exact nativeConformalSubgroupMobiusHom_action _
    (cofiniteMixedTangentialGenerated_conformal θ d hθ hd hb ρ hρ hθρ) g z

/-- The faithful projective group has the literal original polygon as fundamental domain. -/
theorem cofiniteMixedTangential_projective_native_fundamental :
    letI:=(cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod).nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ)
      ℍ MeasureTheory.volume
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior) := by
  let originalAction:=
    (cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod).nativeAction
  let e:=cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ
  have he (g:cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ) (z:ℍ) :
      (Homeomorph.refl ℍ) (g • z)=e.symm g • (Homeomorph.refl ℍ) z := by
    change g • z=(e.symm g).val z
    simpa only [e,MulEquiv.apply_symm_apply] using
      cofiniteMixedTangentialGroupEquiv_action θ d hθ hd hb ρ hρ hθρ hPeriod (e.symm g) z
  have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e.symm (Homeomorph.refl ℍ) he
    (cofiniteTangential_mixed_poincare θ d hθ hd hb ρ hρ hθρ hPeriod).2
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain _ ℍ
    (MeasureTheory.Measure.map id MeasureTheory.volume) (id ⁻¹' _) at h
  simpa only [MeasureTheory.Measure.map_id,preimage_id] using h

/-- The original polygon is a fundamental domain in the actual projective Cayley disc. -/
theorem cofiniteMixedTangential_projective_disc_fundamental :
    let P:=cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
    IsFuchsianFundamentalDomain P.cayleyData
      (P.cayleyCoordinate ''
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior)) := by
  exact (cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod).cayley_fundamental
    (cofiniteMixedTangential_projective_native_fundamental θ d hθ hd hb ρ hρ hθρ hPeriod)

/-- The finite coordinate of this actual domain is exactly the original polygon interior. -/
theorem cofiniteMixedTangential_projective_disc_finite_region :
    let P:=cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
    P.cayleyData.finiteCoordinate '' (P.cayleyCoordinate ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior))=
        (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb).interior := by
  dsimp only
  rw [image_image]
  simp_rw [HalfPlaneFuchsianGroup.cayleyCoordinate_finite]
  exact image_preimage_eq _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.surjective

end ProjectiveModel
end LowDimensionalTopology.Geometry.Fuchsian


namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology

local instance mixedTangentialSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance mixedTangentialSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

section MixedPolygon
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,0<θ i→∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)

include hPeriod

local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "S₀" => cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
local notation "P₀" => cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => f₀ '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q₀)
local notation "E₀" => MulEquiv.trans (cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ)
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))

/-- The same actual cusp charts yield an injective developing evaluation,
including on every closed side and every finite vertex. -/
theorem cofiniteMixedTangential_evaluation_injective : Function.Injective (S₀).evaluation := by
  have hA6:=cofiniteTangential_mixed_local_tessellation θ d hθ hd hb ρ hρ hθρ hPeriod
  obtain ⟨ε,hε,hCharts⟩:=cofiniteTangential_uniform_charts_of_cusp_sections θ d hθ hd hb ρ hρ hθρ
    (cofiniteTangentialIdealFrame θ d hθ hd hb ρ hθρ)
    (cofiniteTangentialIdealFrame_center θ d hθ hd hb ρ hθρ)
    (cofiniteTangentialIdealFrame_vertex θ d hθ hd hb ρ hθρ)
    (cofiniteTangentialIdealHeight θ d hθ hd hb ρ hθρ)
    (cofiniteTangentialIdealHeight_spec θ d hθ hd hb ρ hθρ).1 hA6
    (cofiniteTangentialIdeal_openPartialHomeomorph θ d hθ hd hb ρ hρ hθρ hA6)
  choose chart hmem htarget hmap using hCharts
  exact (hA6.evaluation_homeomorph_of_uniform_charts (S₀)
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_interior_isConnected Q₀)
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier Q₀).le hε ⟨chart,hmem,htarget,hmap⟩).injective

/-- The faithful projective coordinate uses the very same physical maps. -/
theorem cofiniteMixedTangential_coordinate_action (g:(S₀).Generated) (z:ℍ) :
    f₀ (g.val z)=E₀ g • f₀ z := by
  have h:=(P₀).cayleyCoordinate_equivariant
    (cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ g) z
  rw [cofiniteMixedTangentialGroupEquiv_action θ d hθ hd hb ρ hρ hθρ hPeriod] at h
  exact h

/-- The original finite or cusped polygon has a nontrivial true neighbor at
every finite boundary point; local finiteness is a conclusion. -/
theorem cofiniteMixedTangential_projective_disc_convex :
    IsConvexFuchsianPolygon (P₀).cayleyData D₀ := by
  have hFD:=cofiniteMixedTangential_projective_disc_fundamental θ d hθ hd hb ρ hρ hθρ hPeriod
  have hconv:_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex ((P₀).cayleyData.finiteCoordinate '' D₀):=by
    rw [cofiniteMixedTangential_projective_disc_finite_region θ d hθ hd hb ρ hρ hθρ hPeriod]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb
  refine ⟨(convex_fundamentalDomain_locallyFinite_iff_boundary_mates
    (P₀).cayleyData D₀ hFD hconv).mpr ?_,hconv⟩
  intro y hy
  have hy':y∈f₀ '' frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (Q₀).interior):=by
    rwa [(f₀).image_frontier]
  obtain ⟨x,hx,rfl⟩:=hy'
  have hxB:x∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).boundary:=by
    rwa [←_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_frontier_boundary Q₀]
  obtain ⟨s,hs,hxs⟩:=mem_sUnion.mp hxB
  let t:(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).Side:=⟨s,hs⟩
  let g:(S₀).Generated:=(S₀).generator t
  refine ⟨E₀ g,?_,?_⟩
  · intro he
    have hge:g=1:=(E₀).injective (he.trans (map_one E₀).symm)
    obtain ⟨i,hi⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀).surjective t
    have hg:cofiniteTangentPairingElement θ d hθ hd hb i (ρ i)=1:=by
      have hh:=congrArg Subtype.val hge
      change (S₀).element t=1 at hh
      rw [←hi,cofiniteTangentialJordanSidePairing_element_index] at hh
      exact hh
    exact cofiniteTangentPairingElement_ne_one θ d hθ hd hb i (ρ i) hg
  · rw [←cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod]
    rw [←(f₀).image_frontier]
    refine mem_image_of_mem f₀ ?_
    change g.val x∈frontier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).interior
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_frontier_boundary Q₀]
    apply (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).side_subset_boundary ((S₀).paired t)
    rw [←(S₀).generator_side_image t]
    exact ⟨x,hxs,rfl⟩

/-- The physical density area is the original prescribed angle defect,
also for ideal zero-angle corners. -/
theorem cofiniteMixedTangential_projective_disc_area :
    (P₀).cayleyData.area D₀=(Q₀).area := by
  have hopen:=(cofiniteMixedTangential_projective_disc_fundamental
    θ d hθ hd hb ρ hρ hθρ hPeriod).isOpen
  rw [(P₀).cayleyData.area_apply _ hopen.measurableSet,
    cofiniteMixedTangential_projective_disc_finite_region θ d hθ hd hb ρ hρ hθρ hPeriod]
  rfl

theorem cofiniteMixedTangential_projective_disc_area_exact :
    (P₀).cayleyData.area D₀=ENNReal.ofReal (((n:ℝ)-2)*Real.pi-∑i:Fin n,θ i) := by
  rw [cofiniteMixedTangential_projective_disc_area θ d hθ hd hb ρ hρ hθρ hPeriod,
    _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.area_eq_original_angle_defect]
  simp_rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]

theorem cofiniteMixedTangential_projective_disc_area_lt_top :
    (P₀).cayleyData.area D₀<⊤ := by
  rw [cofiniteMixedTangential_projective_disc_area θ d hθ hd hb ρ hρ hθρ hPeriod]
  exact (Q₀).area_lt_top

end MixedPolygon
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The actual inward side component is precisely the true global support
cut, selected by the physical common incircle center. -/
theorem cofiniteMixedTangential_inward_support_iff {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
 (i:Fin n) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let B:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb)
      (fun j=>by rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle];exact (hθ j).2)
    ∀z:ℍ,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i) UpperHalfPlane.I ↔
      inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤B.offsets i := by
  dsimp only
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
  have hQ:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb
  have ha:∀j,Q.angle j<Real.pi:=by intro j;rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle];exact (hθ j).2
  let B:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha
  have hII:UpperHalfPlane.I∈P.interior:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I∈Q.interior
    have hz:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=0:=by
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    rw [hz]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_origin_mem θ d hθ hd hb
  have hIle:inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate UpperHalfPlane.I)≤B.offsets i:=
    (cofiniteJordan_carrier_support_iff Q hQ ha UpperHalfPlane.I).mp
      (P.interior_subset_carrier hII) i
  have hIlt:inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate UpperHalfPlane.I)<B.offsets i:=by
    apply lt_of_le_of_ne hIle
    intro he
    exact cofiniteTangential_side_avoids_origin θ d hθ hd hb i
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha i UpperHalfPlane.I).mpr he)
  have hm:B.normals i≠0:=by
    intro he
    have hh:=B.normal_norm i
    rw [he,norm_zero] at hh
    norm_num at hh
  have hCut:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlane_eq_le (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i) (B.normals i) (B.offsets i) hm
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_line_support_iff Q hQ ha i) UpperHalfPlane.I hIlt
  intro z
  exact (Set.ext_iff.mp hCut) z

/-- The literal actual neighboring tile meets the original closed polygon
in exactly the original whole side, with no pre-assumed side identification. -/
theorem cofiniteMixedTangentPairing_carrier_intersection {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)

    (i j:Fin n) (hl:θ i=θ (finRotate n j)) (hr:θ (finRotate n i)=θ j) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
    P.carrier∩(cofiniteTangentPairingElement θ d hθ hd hb i j) ⁻¹' P.carrier=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q
  have hQ:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb
  have ha:∀k,Q.angle k<Real.pi:=by intro k;rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle];exact (hθ k).2
  let B:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSupports Q hQ ha
  let N:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
  have hPcut:∀k:Fin n,P.carrier⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k) UpperHalfPlane.I:=by
    intro k z hz
    apply (cofiniteMixedTangential_inward_support_iff θ d hθ hd hb k z).mpr
    exact (cofiniteJordan_carrier_support_iff Q hQ ha z).mp hz k
  ext z
  constructor
  · rintro ⟨hz,hAz⟩
    have hRz:N.reflection z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N UpperHalfPlane.I:=
      (cofiniteTangentMirror_native_inward_iff θ d hθ hd hb i j hl hr _).mp (hPcut j hAz)
    have hcutR:inner ℝ (B.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (N.reflection z))≤B.offsets i:=
      (cofiniteMixedTangential_inward_support_iff θ d hθ hd hb i _).mp hRz
    obtain ⟨σ,hσ,hCut⟩:=cofiniteJordan_side_signed_support Q hQ ha i
    have hpos:0≤σ*N.normalTimeAt z:=(hCut z).mpr
      ((cofiniteJordan_carrier_support_iff Q hQ ha z).mp hz i)
    have hneg:0≤σ*N.normalTimeAt (N.reflection z):=(hCut _).mpr hcutR
    have hunit:N.normalPairing N=1:=by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalPairing,real_inner_self_eq_norm_sq]
      nlinarith only [N.incenterNormal_lorentz_unit]
    rw [N.normalTimeAt_reflection N z,hunit] at hneg
    have hzero:σ*N.normalTimeAt z=0:=by nlinarith only [hpos,hneg]
    have hline:z∈N.carrier:=(N.normalTimeAt_eq_zero_iff z).mp ((mul_eq_zero.mp hzero).resolve_left hσ)
    rw [cofiniteJordan_side_eq_carrier_inter_line Q hQ ha i]
    exact ⟨hz,hline⟩
  · intro hz
    have hA:cofiniteTangentPairingElement θ d hθ hd hb i j z∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q j:=by
      rw [←cofiniteTangentPairingElement_side_image θ d hθ hd hb i j hl hr]
      exact mem_image_of_mem _ hz
    exact ⟨P.side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i) hz,
      P.side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q j) hA⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- Pairing a true finite side nonvertex cannot create a finite vertex,
even when one or both original side endpoints are ideal. -/
theorem cofiniteJordan_pairing_nonvertex {n:ℕ} (Q:_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (S:_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q))
    (i:Fin n) {x:ℍ} (hx:x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i)
    (hv:x∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q) :
    S.element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i) x∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q := by
  let s:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i
  intro he
  have hside:S.element s x∈(S.paired s).val:=by
    rw [←S.side_image s]
    exact ⟨x,hx,rfl⟩
  have h:=cofiniteJordan_pairing_preserves_vertices Q S _ he (S.paired s) hside
  rw [S.element_paired] at h
  change (S.element s)⁻¹ ((S.element s) x)∈_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q at h
  change (S.element s).symm ((S.element s) x)∈_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q at h
  rw [(S.element s).symm_apply_apply] at h
  exact hv h

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

section OriginalSides
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,0<θ i→∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
include hPeriod
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "S₀" => cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
local notation "P₀" => cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => f₀ '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q₀)
local notation "E₀" => MulEquiv.trans (cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ)
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))
local notation "hD₀" => cofiniteMixedTangential_projective_disc_convex θ d hθ hd hb ρ hρ hθρ hPeriod

/-- Every whole-group closed-tile incidence at a nonvertex is the identity or its unique original side crossing. -/
theorem cofiniteMixedTangential_nonvertex_closed_incidence (x:ℍ)
    (hx:x∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier)
    (hv:x∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀) (g:(S₀).Generated) (y:ℍ)
    (hy:y∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier) (hgy:g.val y=x) :
    g=1 ∨ ∃i:Fin n,x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i ∧ g=((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i))⁻¹ := by
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀
  let S:=S₀
  let p:P.Point:=⟨x,hx⟩
  let q:P.Point:=⟨y,hy⟩
  have hproj:S.project (g,q)=S.project (1,p):=by
    apply cofiniteMixedTangential_evaluation_injective θ d hθ hd hb ρ hρ hθρ hPeriod
    exact hgy
  have hm:(g,q)∈S.project ⁻¹' {S.project (1,p)}:=hproj
  by_cases hI:x∈P.interior
  · rw [S.project_fiber_eq_singleton_of_interior (1,p) hI] at hm
    exact Or.inl (congrArg Prod.fst hm)
  · have hB:x∈P.boundary:=hx.resolve_left hI
    obtain ⟨_,⟨i,rfl⟩,hi⟩:=mem_sUnion.mp hB
    let s:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i
    have hmate:=cofiniteJordan_pairing_nonvertex Q₀ S i hi hv
    have hu:∀t:P.Side,x∈t.val→t=s:=by
      intro t ht
      obtain ⟨j,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀).surjective t
      by_cases he:i=j
      · exact congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀) he.symm
      · exact (hv (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q₀ he hi ht)).elim
    have hw:∀t:P.Side,(S.sideMateCopy (1,p) s hi).2.val∈t.val→t=S.paired s:=by
      intro t ht
      let v:=S.generator s • x
      have hvp:v∈(S.paired s).val:=by rw [←S.generator_side_image];exact ⟨x,hi,rfl⟩
      obtain ⟨j,hj⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀).surjective (S.paired s)
      obtain ⟨l,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀).surjective t
      by_cases he:j=l
      · exact (congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀) he.symm).trans hj
      · have hvj:v∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ j:=by change v∈((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀) j).val;rw [hj];exact hvp
        exact (hmate (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q₀ he hvj ht)).elim
    rw [S.project_fiber_eq_side_pair (1,p) s hi hu hw] at hm
    rcases hm with he|he
    · exact Or.inl (congrArg Prod.fst he)
    · exact Or.inr ⟨i,hi,by simpa only [_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.sideMateCopy,one_mul] using congrArg Prod.fst he⟩

/-- The literal closed native carrier maps exactly to the original domain closure. -/
theorem cofiniteMixedTangential_original_carrier_image :
    f₀ '' (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier=closure D₀ := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier Q₀]
  exact (f₀).image_closure _

/-- The actual original side is the true intersection with the inverse-pairing neighbor. -/
theorem cofiniteMixedTangential_original_side_intersection (i:Fin n) :
    f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i=closure D₀ ∩
      fuchsianDomainTile (P₀).cayleyData D₀ (E₀ (((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i))⁻¹)) := by
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀
  let g:=(S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)
  have hcut:P.carrier∩g.val ⁻¹' P.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i:=by
    change P.carrier∩(S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i) ⁻¹' P.carrier=_
    rw [cofiniteTangentialJordanSidePairing_element_index θ d hθ hd hb ρ hρ hθρ i]
    exact cofiniteMixedTangentPairing_carrier_intersection θ d hθ hd hb i (ρ i)
      (hθρ i) (cofiniteTangentialPairing_other_angle θ ρ hρ hθρ i)
  change f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i=closure D₀ ∩ (fun z=>E₀ g⁻¹ • z) '' closure D₀
  rw [←cofiniteMixedTangential_original_carrier_image θ d hθ hd hb ρ hρ hθρ hPeriod]
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hxP:x∈P.carrier∩g.val ⁻¹' P.carrier:=hcut.symm ▸ hx
    refine ⟨⟨x,hxP.1,rfl⟩,f₀ (g.val x),⟨g.val x,hxP.2,rfl⟩,?_⟩
    have he:=cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod g⁻¹ (g.val x)
    exact he.symm.trans (congrArg f₀ (inv_smul_smul g x))
  · rintro ⟨⟨x,hx,rfl⟩,w,⟨y,hy,rfl⟩,he⟩
    have hyx:g⁻¹ • y=x:=(f₀).injective
      ((cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod g⁻¹ y).trans he)
    have hxy:g.val x=y:=by rw [←hyx];exact smul_inv_smul g y
    refine ⟨x,hcut ▸ And.intro hx ?_,rfl⟩
    change g.val x∈P.carrier
    rwa [hxy]

omit hPeriod in
/-- No original side generator is the identity in the entire native group. -/
theorem cofiniteMixedTangential_original_generator_ne_one (i:Fin n) :
    (S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)≠1 := by
  intro he
  have h:(S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)=1:=congrArg Subtype.val he
  rw [cofiniteTangentialJordanSidePairing_element_index θ d hθ hd hb ρ hρ hθρ i] at h
  exact cofiniteTangentPairingElement_ne_one θ d hθ hd hb i (ρ i) h

/-- Each original labelled whole side is a genuine side of the actual Fuchsian polygon. -/
def cofiniteMixedTangentialOriginalSide (i:Fin n) : FuchsianPolygonSides (P₀).cayleyData D₀ := by
  refine ⟨f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i,?_⟩
  have hn:(f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i).Nontrivial:=by
    have hbase:(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i).Nontrivial:=
      _root_.LowDimensionalTopology.Geometry.Polygon.nativeCompactifiedSide_nontrivial ((Q₀).vertices i) ((Q₀).vertices (finRotate n i))
        ((Q₀).vertices_injective.ne ((Q₀).next_ne_self i).symm)
    exact hbase.image (f₀).injective
  rw [cofiniteMixedTangential_original_side_intersection θ d hθ hd hb ρ hρ hθρ hPeriod i] at hn ⊢
  apply (hD₀).side_of_nontrivial_intersection ?_ hn
  intro he
  apply inv_ne_one.mpr (cofiniteMixedTangential_original_generator_ne_one θ d hθ hd hb ρ hρ hθρ i)
  apply (E₀).injective
  exact he.trans (E₀).map_one.symm

theorem cofiniteMixedTangentialOriginalSide_element (i:Fin n) :
    fuchsianSideElement hD₀ (cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod i)=
      E₀ (((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i))⁻¹) := by
  apply ((hD₀).existsUnique_side_element
    (cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod i).property).unique
      (fuchsianSideElement_spec hD₀ _)
  constructor
  · intro he
    apply inv_ne_one.mpr (cofiniteMixedTangential_original_generator_ne_one θ d hθ hd hb ρ hρ hθρ i)
    apply (E₀).injective
    exact he.trans (E₀).map_one.symm
  · exact cofiniteMixedTangential_original_side_intersection θ d hθ hd hb ρ hρ hθρ hPeriod i

theorem cofiniteMixedTangentialOriginalSide_injective :
    Function.Injective (cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod) := by
  intro i j he
  apply _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSide_injective Q₀
  exact (f₀).injective.image_injective (congrArg Subtype.val he)

/-- Actual positive-length sides cannot be hidden among the finitely many original vertices. -/
theorem cofiniteMixedTangentialOriginalSide_surjective :
    Function.Surjective (cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod) := by
  intro s
  let f:=f₀
  let E:=E₀
  let V:Set (P₀).cayleyData.domain.carrier:=f '' _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀
  have hV:V.Finite:=(_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices_finite Q₀).image f
  let :T2Space (P₀).cayleyData.domain.carrier:=f.symm.isEmbedding.t2Space
  have hpre:IsPreconnected s.val:=
    (P₀).cayleyData.finiteCoordinate.isEmbedding.isInducing.isPreconnected_image.mp
      s.property.2.1.1.isPreconnected
  have hinf:s.val.Infinite:=hpre.infinite_of_nontrivial s.property.2.2
  have hex:∃z∈s.val,z∉V:=by
    by_contra he
    apply hinf
    apply hV.subset
    intro z hz
    by_contra hzV
    exact he ⟨z,hz,hzV⟩
  obtain ⟨z,hz,hzV⟩:=hex
  have hzC:z∈closure D₀:=((fuchsianSideElement_spec hD₀ s).2 ▸ hz).1
  rw [←cofiniteMixedTangential_original_carrier_image θ d hθ hd hb ρ hρ hθρ hPeriod] at hzC
  obtain ⟨x,hx,rfl⟩:=hzC
  have hv:x∉_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀:=by
    intro hv
    exact hzV ⟨x,hv,rfl⟩
  have hzT:f x∈fuchsianDomainTile (P₀).cayleyData D₀ (fuchsianSideElement hD₀ s):=
    ((fuchsianSideElement_spec hD₀ s).2 ▸ hz).2
  obtain ⟨w,hw,hew⟩:=hzT
  rw [←cofiniteMixedTangential_original_carrier_image θ d hθ hd hb ρ hρ hθρ hPeriod] at hw
  obtain ⟨y,hy,rfl⟩:=hw
  let g:=E.symm (fuchsianSideElement hD₀ s)
  have hgy:g.val y=x:=by
    apply f.injective
    rw [cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod,E.apply_symm_apply]
    exact hew
  rcases cofiniteMixedTangential_nonvertex_closed_incidence θ d hθ hd hb ρ hρ hθρ hPeriod
      x hx hv g y hy hgy with he|⟨i,_hxi,he⟩
  · exact False.elim ((fuchsianSideElement_spec hD₀ s).1
      ((E.apply_symm_apply _).symm.trans ((congrArg E he).trans E.map_one)))
  · refine ⟨i,?_⟩
    apply fuchsianSideElement_injective hD₀
    rw [cofiniteMixedTangentialOriginalSide_element θ d hθ hd hb ρ hρ hθρ hPeriod i]
    have h:=congrArg E he
    rw [E.apply_symm_apply] at h
    exact h.symm

/-- The original finite side labels enumerate all actual Fuchsian sides exactly once. -/
def cofiniteMixedTangentialOriginalSideEquiv : Fin n ≃ FuchsianPolygonSides (P₀).cayleyData D₀ :=
  Equiv.ofBijective (cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod)
    ⟨cofiniteMixedTangentialOriginalSide_injective θ d hθ hd hb ρ hρ hθρ hPeriod,
      cofiniteMixedTangentialOriginalSide_surjective θ d hθ hd hb ρ hρ hθρ hPeriod⟩

/-- Original actual side pairing is precisely the unchanged literal involution on its labels. -/
theorem cofiniteMixedTangentialOriginalSide_paired (i:Fin n) :
    fuchsianPairedSide hD₀ (cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod i)=
      cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod (ρ i) := by
  apply fuchsianSideElement_injective hD₀
  rw [fuchsianSideElement_paired,
    cofiniteMixedTangentialOriginalSide_element θ d hθ hd hb ρ hρ hθρ hPeriod i,
    cofiniteMixedTangentialOriginalSide_element θ d hθ hd hb ρ hρ hθρ hPeriod (ρ i)]
  have hp:=(S₀).generator_paired (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)
  rw [cofiniteTangentialJordanSidePairing_paired_index θ d hθ hd hb ρ hρ hθρ i] at hp
  simp only [hp,map_inv,inv_inv]

/-- The actual self-paired sides retain exactly their original fixed occurrence labels. -/
def cofiniteMixedTangentialOriginalSelfSideEquiv :
    {i:Fin n //ρ i=i} ≃ {s:FuchsianPolygonSides (P₀).cayleyData D₀ //fuchsianPairedSide hD₀ s=s} :=
  (cofiniteMixedTangentialOriginalSideEquiv θ d hθ hd hb ρ hρ hθρ hPeriod).subtypeEquiv (fun i=>by
    change ρ i=i ↔ fuchsianPairedSide hD₀
      (cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod i)=
        cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod i
    rw [cofiniteMixedTangentialOriginalSide_paired θ d hθ hd hb ρ hρ hθρ hPeriod i]
    exact (cofiniteMixedTangentialOriginalSide_injective θ d hθ hd hb ρ hρ hθρ hPeriod).eq_iff.symm)

theorem cofiniteMixedTangential_original_side_card : Nat.card (FuchsianPolygonSides (P₀).cayleyData D₀)=n := by
  rw [←Nat.card_congr (cofiniteMixedTangentialOriginalSideEquiv θ d hθ hd hb ρ hρ hθρ hPeriod)]
  exact Nat.card_fin n

/-- Subdividing each true self-side once gives exactly raw sides plus actual fixed labels. -/
theorem cofiniteMixedTangential_original_refined_side_card :
    Nat.card (OriginalRefinedSide hD₀)=n+Nat.card {i:Fin n //ρ i=i} := by
  rw [originalRefinedSide_card hD₀
    (ne_of_lt (cofiniteMixedTangential_projective_disc_area_lt_top θ d hθ hd hb ρ hρ hθρ hPeriod)),
    cofiniteMixedTangential_original_side_card θ d hθ hd hb ρ hρ hθρ hPeriod,
    ←Nat.card_congr (cofiniteMixedTangentialOriginalSelfSideEquiv θ d hθ hd hb ρ hρ hθρ hPeriod)]

end OriginalSides
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology

section MixedClosedSides
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,0<θ i→∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
include hPeriod
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "S₀" => cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
local notation "P₀" => cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => f₀ '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q₀)
local notation "E₀" => MulEquiv.trans (cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ)
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))
local notation "hD₀" => cofiniteMixedTangential_projective_disc_convex θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "side₀" => cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod

/-- The whole original compactified side, including all ideal endpoints,
is exactly the unchanged prescribed closed geodesic segment. -/
theorem cofiniteMixedTangentialOriginalSide_closedModel (i:Fin n) :
    fuchsianSideClosedModel (side₀ i)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment ((Q₀).vertices i) ((Q₀).vertices (finRotate n i)) := by
  change closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel '' ((P₀).cayleyData.finiteCoordinate ''
    (f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i)))=_
  rw [image_image,image_image]
  simp_rw [HalfPlaneFuchsianGroup.cayleyCoordinate_finite]
  exact _root_.LowDimensionalTopology.Geometry.Polygon.nativeCompactifiedSide_closedModelClosure ((Q₀).vertices i) ((Q₀).vertices (finRotate n i))
    ((Q₀).vertices_injective.ne ((Q₀).next_ne_self i).symm)

/-- The inverse original side element has precisely the genuine pairing's
closed action, without losing its original ideal endpoints. -/
theorem cofiniteMixedTangentialOriginalSide_closedAction (i:Fin n) (p:𝕔𝔻) :
    ((P₀).cayleyData.compactifiedAction (fuchsianSideElement hD₀ (side₀ i))⁻¹).closedMap p=
      (cofiniteTangentPairingClosedIsometry θ d hθ hd hb i (ρ i)).closedMap p := by
  let g:(S₀).Generated:=(S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)
  have hside:(fuchsianSideElement hD₀ (side₀ i))⁻¹=E₀ g:=by
    rw [cofiniteMixedTangentialOriginalSide_element θ d hθ hd hb ρ hρ hθρ hPeriod,map_inv,inv_inv]
  rw [hside]
  let :T2Space 𝕔𝔻:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.isEmbedding.t2Space
  have hfun:(fun p:𝕔𝔻=>((P₀).cayleyData.compactifiedAction (E₀ g)).closedMap p)=
      fun p:𝕔𝔻=>(cofiniteTangentPairingClosedIsometry θ d hθ hd hb i (ρ i)).closedMap p:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.denseRange_discToClosedModel.equalizer
      ((P₀).cayleyData.compactifiedAction (E₀ g)).closedMap.continuous
      (cofiniteTangentPairingClosedIsometry θ d hθ hd hb i (ρ i)).closedMap.continuous
    funext z
    change ((P₀).cayleyData.compactifiedAction (E₀ g)).closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)=
      (cofiniteTangentPairingClosedIsometry θ d hθ hd hb i (ρ i)).closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    let x:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z
    have hcoord:(P₀).cayleyData.finiteCoordinate (f₀ x)=z:=by
      rw [HalfPlaneFuchsianGroup.cayleyCoordinate_finite]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane z
    have hact:(P₀).cayleyData.finiteCoordinate (E₀ g •f₀ x)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (g.val x):=by
      rw [←cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod g x]
      exact (P₀).cayleyCoordinate_finite (g.val x)
    have hg:g.val=cofiniteTangentPairingElement θ d hθ hd hb i (ρ i):=by
      exact cofiniteTangentialJordanSidePairing_element_index θ d hθ hd hb ρ hρ hθρ i
    calc
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ((P₀).cayleyData.finiteCoordinate (E₀ g •f₀ x)):=by
        rw [←hcoord,UnitDiscFuchsianGroup.compactifiedAction_finite]
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (cofiniteTangentPairingElement θ d hθ hd hb i (ρ i) x)):=by
        rw [hact,hg]
      _=_:=by
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes,cofiniteTangentPairingClosedIsometry_finite]
  exact congrFun hfun p

/-- The actual original side pairing reverses its prescribed finite or
ideal endpoints, retaining the complete original label incidence. -/
theorem cofiniteMixedTangentialOriginalSide_endpoints (i:Fin n) :
    let T:=((P₀).cayleyData.compactifiedAction (fuchsianSideElement hD₀ (side₀ i))⁻¹).closedMap
    T ((Q₀).vertices i)=(Q₀).vertices ((ρ.trans (finRotate n)) i) ∧
      T ((Q₀).vertices (finRotate n i))=(Q₀).vertices (ρ i) := by
  constructor
  · rw [cofiniteMixedTangentialOriginalSide_closedAction θ d hθ hd hb ρ hρ hθρ hPeriod]
    exact cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i (ρ i) (hθρ i)
  · rw [cofiniteMixedTangentialOriginalSide_closedAction θ d hθ hd hb ρ hρ hθρ hPeriod]
    exact cofiniteTangentPairingClosedIsometry_vertex_right θ d hθ hd hb i (ρ i)
      (cofiniteTangentialPairing_other_angle θ ρ hρ hθρ i)

end MixedClosedSides
end LowDimensionalTopology.Geometry.Fuchsian


namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
/-- Every admissible actual finite construction attains its exact refined original side count. -/
theorem cofiniteConstruction_mixed_actual_refined_side_count (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,m=0∨2≤m) (hlast:last=0∨2≤last) (hdef:0<cofiniteConstructionDeficit g ms last)
    (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i=>(cofiniteConstructionAngles g ms last)[i]) d=Real.pi) :
    let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=
      fun i=>(cofiniteConstructionAngles g ms last)[i]
    let hθ:∀i:Fin (cofiniteConstructionAngles g ms last).length,θ i∈Ico (0:ℝ) Real.pi:=
      fun i=>cofiniteConstruction_angles_mem g ms last hms hlast hdef _ (List.getElem_mem i.isLt)
    let ρ:=cofiniteConstructionPairing g ms last
    let hρ:=cofiniteConstructionPairing_involutive g ms last
    let hθρ:=cofiniteConstructionPairing_angle_profile g ms last
    let hPeriod:∀i:Fin (cofiniteConstructionAngles g ms last).length,
        0<θ i→∃N:ℕ,3≤N ∧((ρ.trans (finRotate _))^[N]) i=i ∧θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N:=
      cofiniteConstruction_mixed_angular_periods g ms last hms hlast hdef
    let hD:=cofiniteMixedTangential_projective_disc_convex θ d hθ hd hb ρ hρ hθρ hPeriod
    Nat.card (OriginalRefinedSide hD)=4*g+2*ms.length := by
  intro θ hθ ρ hρ hθρ hPeriod hD
  change Nat.card (OriginalRefinedSide
    (cofiniteMixedTangential_projective_disc_convex θ d hθ hd hb ρ hρ hθρ hPeriod))=_
  rw [cofiniteMixedTangential_original_refined_side_card θ d hθ hd hb ρ hρ hθρ hPeriod]
  change (cofiniteConstructionAngles g ms last).length+
    Nat.card {i:Fin (cofiniteConstructionAngles g ms last).length //
      cofiniteConstructionPairing g ms last i=i}=_
  rw [cofiniteConstructionSelfSideLabelEquiv_card,cofiniteConstruction_order_two_occurrence_card]
  exact cofiniteConstruction_refined_count g ms last

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

section ActualIdealFixers
variable {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (ρ : Equiv.Perm (Fin n))
    (hρ : Function.Involutive ρ) (hθρ : ∀ i, θ i = θ (finRotate n (ρ i)))

local notation "F₀" => cofiniteTangentialIdealFrame θ d hθ hd hb ρ hθρ
local notation "τ₀" => ρ.trans (finRotate n)
local notation "c₀" => 2 * Real.sinh d
local notation "W₀" => cofiniteTangentialIdealWord θ d hθ hd hb ρ hθρ
local notation "S₀" => cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
local notation "v₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd

/-- A true positive original label period gives the literal original word
as a genuine parabolic real-SL lift fixing its actual ideal vertex. -/
theorem cofiniteTangential_zero_period_parabolic_fixer (i : Fin n) (hi : θ i = 0)
    (N : ℕ) (hN : 0 < N) (hreturn : (τ₀ ^ N) i = i) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = W₀ i (N : ℤ) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ (S₀).Generated ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm (v₀ i)).val =
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm (v₀ i)).val := by
  let t : ℝ := -(N : ℝ) * c₀
  let A := (F₀ i)⁻¹ * _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t * F₀ i
  have hnative : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = W₀ i (N : ℤ) := by
    change fordSLNativeHom A =
      (fordSLNativeHom (F₀ i))⁻¹ * fordSLNativeHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) *
        fordSLNativeHom (F₀ ((τ₀ ^ (N : ℤ)) i))
    rw [zpow_natCast, hreturn]
    dsimp only [A]
    rw [map_mul, map_mul, map_inv]
  have ht : t ≠ 0 := by
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    have hc : 0 < c₀ := mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sinh_pos_iff.mpr hd)
    exact (mul_neg_of_neg_of_pos (neg_neg_of_pos hNp) hc).ne
  have hproj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F₀ i))⁻¹ *
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t : ℂ) * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F₀ i) := by
    dsimp only [A]
    rw [map_mul, map_mul, map_inv, parabolicSL_translation_projection]
  have hpar : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    have hT := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff (t : ℂ)).mpr (by exact_mod_cast ht)
    apply (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr
      ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F₀ i))⁻¹, by rw [inv_inv]; exact hproj.symm⟩)).mp hT
  have hInf : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F₀ i)).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm (v₀ i)).val = ∞ := by
    rw [← cofiniteSL_closed_halfPlane_value,
      cofiniteTangentialIdealFrame_vertex θ d hθ hd hb ρ hθρ i hi,
      Homeomorph.symm_apply_apply]
    rfl
  refine ⟨A, hnative, ?_, hpar, ?_⟩
  · rw [hnative]
    exact cofiniteTangentialIdealWord_mem θ d hθ hd hb ρ hθρ hρ i hi (N : ℤ)
  · rw [hproj]
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F₀ i)).val.symm
      ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t : ℂ)).val
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F₀ i)).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm (v₀ i)).val)) = _
    rw [hInf, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty, ← hInf, Equiv.symm_apply_apply]

/-- Every actual zero corner has a genuine parabolic fixer in the entire
original raw generated group. Its positive label period is derived from the
finite actual permutation, rather than required as an extra hypothesis. -/
theorem cofiniteTangential_zero_parabolic_fixer (i : Fin n) (hi : θ i = 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ (S₀).Generated ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm (v₀ i)).val =
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm (v₀ i)).val := by
  obtain ⟨A, _hword, hmem, hpar, hfix⟩ := cofiniteTangential_zero_period_parabolic_fixer
    θ d hθ hd hb ρ hρ hθρ i hi (orderOf τ₀) (orderOf_pos τ₀) (by
      rw [pow_orderOf_eq_one]
      rfl)
  exact ⟨A, hmem, hpar, hfix⟩

end ActualIdealFixers
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology
  MeasureTheory
local instance mixedFirstKindSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance mixedFirstKindSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

section MixedFirstKind
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
    (hPeriod:∀i:Fin n,0<θ i→∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧
      θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "S₀" => cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
local notation "P₀" => cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => f₀ '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q₀)
local notation "E₀" => MulEquiv.trans (cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ)
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))

/-- A literal zero corner supplies a genuine parabolic in the entire
original Cayley group, not merely a formal peripheral word. -/
theorem cofiniteMixedTangential_contains_parabolic (i:Fin n) (hi:θ i=0) :
    ∃g:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ),
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val := by
  obtain ⟨A,hA,hpar,_hfix⟩:=cofiniteTangential_zero_parabolic_fixer θ d hθ hd hb ρ hρ hθρ i hi
  let a:(S₀).Generated:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,hA⟩
  refine ⟨E₀ a,?_⟩
  have hproj:cofiniteMixedTangentialToMobius θ d hθ hd hb ρ hρ hθρ a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A:=
    nativeConformalSubgroupMobiusHom_matrix _ _ A hA
  change _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*(cofiniteMixedTangentialToMobius θ d hθ hd hb ρ hρ hθρ a)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)
  rw [hproj]
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius,rfl⟩)).mp hpar

include hPeriod

/-- Genuine finite area and one actual cusp force the whole constructed
group to be non-elementary. -/
theorem cofiniteMixedTangential_nonElementary_of_zero (i:Fin n) (hi:θ i=0) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
      (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ)) := by
  obtain ⟨a,ha⟩:=cofiniteMixedTangential_contains_parabolic θ d hθ hd hb ρ hρ hθρ i hi
  have hFD:=cofiniteMixedTangential_projective_disc_fundamental θ d hθ hd hb ρ hρ hθρ hPeriod
  have hGeo:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))
      (fuchsianGeometricDomain (P₀).cayleyData.asFuchsianDisc).carrier
      (geometricModelArea (P₀).cayleyData.asFuchsianDisc) D₀:=by
    rw [geometricModelArea_asUnitDisc]
    exact hFD
  apply parabolic_finite_area_nonElementary (P₀).cayleyData.asFuchsianDisc a.val a.property ha D₀ hGeo
  rw [geometricModelArea_asUnitDisc]
  exact ne_of_lt (cofiniteMixedTangential_projective_disc_area_lt_top θ d hθ hd hb ρ hρ hθρ hPeriod)

/-- The actual cusped realization has its whole invariant circle as limit
set, with the first-kind condition derived from its genuine finite area. -/
theorem cofiniteMixedTangential_firstKind_of_zero (i:Fin n) (hi:θ i=0) :
    (P₀).cayleyData.asFuchsianDisc.IsFirstKind := by
  have hFD:=cofiniteMixedTangential_projective_disc_fundamental θ d hθ hd hb ρ hρ hθρ hPeriod
  have hGeo:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))
      (fuchsianGeometricDomain (P₀).cayleyData.asFuchsianDisc).carrier
      (geometricModelArea (P₀).cayleyData.asFuchsianDisc) D₀:=by
    rw [geometricModelArea_asUnitDisc]
    exact hFD
  apply fuchsian_finite_area_firstKind (P₀).cayleyData.asFuchsianDisc
    (cofiniteMixedTangential_nonElementary_of_zero θ d hθ hd hb ρ hρ hθρ hPeriod i hi) hGeo
  rw [geometricModelArea_asUnitDisc]
  exact ne_of_lt (cofiniteMixedTangential_projective_disc_area_lt_top θ d hθ hd hb ρ hρ hθρ hPeriod)

/-- The entire realized group is finitely generated, with no presentation
or finite-generation premise added to the construction. -/
theorem cofiniteMixedTangential_finitelyGenerated :
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
      (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ)).FG := by
  have hFD:=cofiniteMixedTangential_projective_disc_fundamental θ d hθ hd hb ρ hρ hθρ hPeriod
  have hGeo:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))
      (fuchsianGeometricDomain (P₀).cayleyData.asFuchsianDisc).carrier
      (geometricModelArea (P₀).cayleyData.asFuchsianDisc) D₀:=by
    rw [geometricModelArea_asUnitDisc]
    exact hFD
  apply finite_area_group_finitelyGenerated (P₀).cayleyData.asFuchsianDisc D₀ hGeo
  rw [geometricModelArea_asUnitDisc]
  exact ne_of_lt (cofiniteMixedTangential_projective_disc_area_lt_top θ d hθ hd hb ρ hρ hθρ hPeriod)

end MixedFirstKind
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The actual original corner relation, generated by the literal natural
vertex step on the unchanged individual labels. -/
def cofiniteConstructionCornerSetoid (g : ℕ) (ms : List ℕ) (last : ℕ) :
    Setoid (Fin (cofiniteConstructionAngles g ms last).length) :=
  Relation.EqvGen.setoid (fun i j => j = cofiniteConstructionVertexStep g ms last i)

/-- The base cycle has one label and each outer occurrence has its own label,
regardless of coincidences between the original numerical angles. -/
def cofiniteConstructionCornerClassMap (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 2 ≤ 4 * g + ms.length) (i : Fin (cofiniteConstructionAngles g ms last).length) :
    Option {j : Fin ms.length // ms[j] ≠ 2} :=
  Sum.elim (fun _ => none) some ((cofiniteConstructionCornerLabelEquiv g ms last hB).symm i)

theorem cofiniteConstructionCornerClassMap_step (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 2 ≤ 4 * g + ms.length) (i : Fin (cofiniteConstructionAngles g ms last).length) :
    cofiniteConstructionCornerClassMap g ms last hB (cofiniteConstructionVertexStep g ms last i) =
      cofiniteConstructionCornerClassMap g ms last hB i := by
  obtain ⟨a, rfl⟩ := (cofiniteConstructionCornerLabelEquiv g ms last hB).surjective i
  rw [cofiniteConstructionCornerLabelEquiv_step]
  cases a <;> simp only [cofiniteConstructionCornerClassMap, Equiv.symm_apply_apply,
    Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, id_eq]

/-- Every original base occurrence is joined to the original base anchor
by the genuine natural-step relation, without using angle values. -/
theorem cofiniteConstruction_base_corner_chain (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 2 ≤ 4 * g + ms.length) (a : Fin (4 * g + ms.length)) :
    (cofiniteConstructionCornerSetoid g ms last).r
      (cofiniteConstructionBaseIndex g ms last ⟨0, by omega⟩)
      (cofiniteConstructionBaseIndex g ms last a) := by
  let b := cofiniteConstructionBaseIndex g ms last (⟨0, by omega⟩ : Fin (4 * g + ms.length))
  have hiter (m : ℕ) : (cofiniteConstructionCornerSetoid g ms last).r b
      ((cofiniteConstructionVertexStep g ms last)^[m] b) := by
    induction m with
    | zero => exact Relation.EqvGen.refl _
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ rfl)
  obtain ⟨m, _hm, heq⟩ := cofiniteConstructionBaseIndex_one_cycle g ms last (by omega) a
  exact heq ▸ hiter m

/-- The complete original natural corner relation identifies exactly the
base marks with one another and each outer occurrence only with itself. -/
theorem cofiniteConstructionCornerClassMap_eq_iff (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 2 ≤ 4 * g + ms.length) (i j : Fin (cofiniteConstructionAngles g ms last).length) :
    cofiniteConstructionCornerClassMap g ms last hB i = cofiniteConstructionCornerClassMap g ms last hB j ↔
      (cofiniteConstructionCornerSetoid g ms last).r i j := by
  constructor
  · intro heq
    obtain ⟨a, rfl⟩ := (cofiniteConstructionCornerLabelEquiv g ms last hB).surjective i
    obtain ⟨b, rfl⟩ := (cofiniteConstructionCornerLabelEquiv g ms last hB).surjective j
    simp only [cofiniteConstructionCornerClassMap, Equiv.symm_apply_apply] at heq
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        change (cofiniteConstructionCornerSetoid g ms last).r
          (cofiniteConstructionBaseIndex g ms last a) (cofiniteConstructionBaseIndex g ms last b)
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (cofiniteConstruction_base_corner_chain g ms last hB a))
          (cofiniteConstruction_base_corner_chain g ms last hB b)
      | inr b => simp at heq
    | inr a =>
      cases b with
      | inl b => simp at heq
      | inr b =>
        have hab : a = b := Option.some.inj heq
        subst b
        exact Relation.EqvGen.refl _
  · intro hij
    induction hij with
    | rel a b hab => exact hab ▸ (cofiniteConstructionCornerClassMap_step g ms last hB a).symm
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The actual original natural corner quotient preserves every separately
marked outer occurrence and has exactly one genuine base class. -/
def cofiniteConstructionCornerClassesEquiv (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 2 ≤ 4 * g + ms.length) :
    Quotient (cofiniteConstructionCornerSetoid g ms last) ≃
      Option {j : Fin ms.length // ms[j] ≠ 2} := by
  let f : Quotient (cofiniteConstructionCornerSetoid g ms last) →
      Option {j : Fin ms.length // ms[j] ≠ 2} :=
    Quotient.lift (cofiniteConstructionCornerClassMap g ms last hB)
      (fun i j hij => (cofiniteConstructionCornerClassMap_eq_iff g ms last hB i j).mpr hij)
  apply Equiv.ofBijective f
  constructor
  · intro q r hqr
    induction q using Quotient.inductionOn with
    | h i =>
      induction r using Quotient.inductionOn with
      | h j =>
        exact Quotient.sound ((cofiniteConstructionCornerClassMap_eq_iff g ms last hB i j).mp hqr)
  · intro a
    cases a with
    | none =>
      refine ⟨Quotient.mk _ (cofiniteConstructionCornerLabelEquiv g ms last hB
        (Sum.inl ⟨0, by omega⟩)), ?_⟩
      exact congrArg (Sum.elim (fun _ => none) some)
        ((cofiniteConstructionCornerLabelEquiv g ms last hB).symm_apply_apply _)
    | some j =>
      refine ⟨Quotient.mk _ (cofiniteConstructionCornerLabelEquiv g ms last hB (Sum.inr j)), ?_⟩
      exact congrArg (Sum.elim (fun _ => none) some)
        ((cofiniteConstructionCornerLabelEquiv g ms last hB).symm_apply_apply _)

/-- The original angle attached to a genuine natural corner class. -/
def cofiniteConstructionCornerClassAngle (g : ℕ) (ms : List ℕ) (last : ℕ)
    (a : Option {j : Fin ms.length // ms[j] ≠ 2}) : ℝ :=
  a.elim (cofiniteConstructionBaseAngle g ms last)
    (fun j => cofiniteConstructionConeAngle ms[j.val])

theorem cofiniteConstructionCornerClassAngle_label (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 2 ≤ 4 * g + ms.length) (i : Fin (cofiniteConstructionAngles g ms last).length) :
    cofiniteConstructionCornerClassAngle g ms last (cofiniteConstructionCornerClassMap g ms last hB i) =
      (cofiniteConstructionAngles g ms last)[i] := by
  obtain ⟨a, rfl⟩ := (cofiniteConstructionCornerLabelEquiv g ms last hB).surjective i
  cases a with
  | inl a =>
    rw [cofiniteConstructionCornerClassMap, Equiv.symm_apply_apply]
    change cofiniteConstructionBaseAngle g ms last =
      (cofiniteConstructionAngles g ms last)[cofiniteConstructionBaseIndex g ms last a]
    exact (cofiniteConstructionBaseIndex_angle g ms last a).symm
  | inr j =>
    rw [cofiniteConstructionCornerClassMap, Equiv.symm_apply_apply]
    change cofiniteConstructionConeAngle ms[j.val] =
      (cofiniteConstructionAngles g ms last)[cofiniteConstructionOuterIndex g ms last j]
    exact (cofiniteConstructionOuterIndex_angle g ms last j).symm

/-- Zero angles are exactly the original zero-order marks, including the
base mark and each separately labelled outer occurrence. -/
theorem cofiniteConstructionCornerClassAngle_zero_iff (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 2 ≤ 4 * g + ms.length) (a : Option {j : Fin ms.length // ms[j] ≠ 2}) :
    cofiniteConstructionCornerClassAngle g ms last a = 0 ↔
      a.elim (last = 0) (fun j => ms[j.val] = 0) := by
  have hnum : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hden : ((4 * g + ms.length : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 4 * g + ms.length ≠ 0)
  cases a with
  | none =>
    simp only [cofiniteConstructionCornerClassAngle, Option.elim_none, cofiniteConstructionBaseAngle,
      cofiniteConstructionConeAngle, div_eq_zero_iff, hnum, hden, false_or, or_false, Nat.cast_eq_zero]
  | some j =>
    simp only [cofiniteConstructionCornerClassAngle, Option.elim_some, cofiniteConstructionConeAngle,
      div_eq_zero_iff, hnum, false_or, Nat.cast_eq_zero]

/-- The angle of an original natural quotient class, with its exact literal
angle on every original representative. -/
def cofiniteConstructionCornerQuotientAngle (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 2 ≤ 4 * g + ms.length) (q : Quotient (cofiniteConstructionCornerSetoid g ms last)) : ℝ :=
  cofiniteConstructionCornerClassAngle g ms last (cofiniteConstructionCornerClassesEquiv g ms last hB q)

theorem cofiniteConstructionCornerQuotientAngle_mk (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 2 ≤ 4 * g + ms.length) (i : Fin (cofiniteConstructionAngles g ms last).length) :
    cofiniteConstructionCornerQuotientAngle g ms last hB (Quotient.mk _ i) =
      (cofiniteConstructionAngles g ms last)[i] :=
  cofiniteConstructionCornerClassAngle_label g ms last hB i

/-- The original zero-angle natural classes are in exact bijection with the
original zero-order base mark and the individual zero-order list occurrences. -/
def cofiniteConstructionZeroCornerClassesEquiv (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hB : 2 ≤ 4 * g + ms.length) :
    {q : Quotient (cofiniteConstructionCornerSetoid g ms last) //
      cofiniteConstructionCornerQuotientAngle g ms last hB q = 0} ≃
      ({_u : Unit // last = 0} ⊕ {j : Fin ms.length // ms[j] = 0}) := by
  let E : {q : Quotient (cofiniteConstructionCornerSetoid g ms last) //
      cofiniteConstructionCornerQuotientAngle g ms last hB q = 0} ≃
      {a : Option {j : Fin ms.length // ms[j] ≠ 2} //
        cofiniteConstructionCornerClassAngle g ms last a = 0} :=
    Equiv.subtypeEquiv (cofiniteConstructionCornerClassesEquiv g ms last hB) (fun _ => Iff.rfl)

  let F : {a : Option {j : Fin ms.length // ms[j] ≠ 2} //
      cofiniteConstructionCornerClassAngle g ms last a = 0} ≃
      ({_u : Unit // last = 0} ⊕ {j : Fin ms.length // ms[j] = 0}) :=
    { toFun := fun a => match ha : a.val with
        | none => Sum.inl ⟨(), (cofiniteConstructionCornerClassAngle_zero_iff g ms last hB none).mp
            (ha ▸ a.property)⟩
        | some j => Sum.inr ⟨j.val, (cofiniteConstructionCornerClassAngle_zero_iff g ms last hB (some j)).mp
            (ha ▸ a.property)⟩
      invFun := fun a => match a with
        | Sum.inl u => ⟨none, (cofiniteConstructionCornerClassAngle_zero_iff g ms last hB none).mpr u.property⟩
        | Sum.inr j => ⟨some ⟨j.val, by rw [j.property]; decide⟩,
            (cofiniteConstructionCornerClassAngle_zero_iff g ms last hB _).mpr j.property⟩
      left_inv := by
        rintro ⟨a, ha⟩
        cases a <;> rfl
      right_inv := by
        intro a
        cases a with
        | inl u => apply congrArg Sum.inl; exact Subtype.ext (Subsingleton.elim _ _)
        | inr j => apply congrArg Sum.inr; rfl }
  exact E.trans F

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

section ActualRawIdealLabels
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {n : ℕ} (V : Fin n → 𝕔𝔻) (hV : Function.Injective V)
    (hnext : ∀ i, finRotate n i ≠ i) (E : Fin n ≃ FuchsianPolygonSides P D)
    (hside : ∀ i, fuchsianSideClosedModel (E i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (V i) (V (finRotate n i)))

include E hside hV hnext

/-- At genuine ideal points, the unchanged original marked polygon vertices
are exactly the genuine original refined endpoints. Finite self-side centers
cannot contribute an extra ideal label. -/
theorem cofinite_raw_ideal_endpoint_iff (z : 𝕔𝔻) (hz : ‖(z : ℂ)‖ = 1) :
    z ∈ Set.range V ↔ z ∈ originalRefinedEndpointSet hD := by
  constructor
  · rintro ⟨i, rfl⟩
    have hmem : V i ∈ fuchsianSideClosedModel (E i) := by
      rw [hside, ← _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedModelSegmentParam]
      exact ⟨0, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelSegmentParam_zero _ _⟩
    obtain ⟨v, _hv, hvz⟩ := OriginalRefinedSide.exists_over_side hD (E i) (V i) hmem
    have hend := original_segment_ideal_eq_endpoint v.leftEndpoint v.rightEndpoint
      (V i) v.endpoints_ne (v.carrier_eq_endpoints ▸ hvz) hz
    rcases hend with hl | hr
    · exact Or.inl ⟨v, hl.symm⟩
    · exact Or.inr ⟨v, hr.symm⟩
  · intro hzE
    have hsome : ∃ v : OriginalRefinedSide hD, z ∈ v.carrier := by
      rcases hzE with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact ⟨v, v.endpoints_mem_carrier.1⟩
      · exact ⟨v, v.endpoints_mem_carrier.2⟩
    obtain ⟨v, hvz⟩ := hsome
    let i := E.symm v.val.1
    have hzS : z ∈ fuchsianSideClosedModel (E i) := by
      rw [show E i = v.val.1 from E.apply_symm_apply _]
      exact v.carrier_subset_original hvz
    rw [hside] at hzS
    have hend := original_segment_ideal_eq_endpoint (V i) (V (finRotate n i)) z
      (hV.ne (hnext i).symm) hzS hz
    rcases hend with hl | hr
    · exact ⟨i, hl.symm⟩
    · exact ⟨finRotate n i, hr.symm⟩

/-- The ideal corners in the original polygon and in the actual refined
cyclic model correspond by equality of their actual closed-disc points. -/
theorem cofinite_raw_ideal_vertex_labels (J : PolygonalCircle)
    (hv : ∀ p, J.IsVertexPoint p ↔ p ∈ _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD) :
    ∃ L : {i : Fin n // ‖(V i : ℂ)‖ = 1} ≃
        {k : ZMod J.n // ‖(originalCyclicVertex hD J hv k : ℂ)‖ = 1},
      ∀ i, originalCyclicVertex hD J hv (L i).val = V i.val := by
  have hex (i : {i : Fin n // ‖(V i : ℂ)‖ = 1}) :
      ∃ k : ZMod J.n, originalCyclicVertex hD J hv k = V i.val := by
    apply Set.mem_range.mp
    rw [range_originalCyclicVertex]
    exact (cofinite_raw_ideal_endpoint_iff hD V hV hnext E hside _ i.property).mp (Set.mem_range_self i.val)
  let f : {i : Fin n // ‖(V i : ℂ)‖ = 1} →
      {k : ZMod J.n // ‖(originalCyclicVertex hD J hv k : ℂ)‖ = 1} := fun i =>
    ⟨Classical.choose (hex i), by rw [Classical.choose_spec (hex i)]; exact i.property⟩
  have hf (i : {i : Fin n // ‖(V i : ℂ)‖ = 1}) :
      originalCyclicVertex hD J hv (f i).val = V i.val := Classical.choose_spec (hex i)
  have hfi : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply hV
    exact (hf i).symm.trans ((congrArg (fun k => originalCyclicVertex hD J hv k.val) hij).trans (hf j))
  have hfs : Function.Surjective f := by
    intro k
    have hmem := (cofinite_raw_ideal_endpoint_iff hD V hV hnext E hside _ k.property).mpr
      (originalCyclicVertex_mem_endpointSet hD J hv k.val)
    obtain ⟨i, hi⟩ := hmem
    let i' : {i : Fin n // ‖(V i : ℂ)‖ = 1} := ⟨i, by rw [hi]; exact k.property⟩
    refine ⟨i', Subtype.ext ?_⟩
    apply originalCyclicVertex_injective hD J hv
    exact (hf i').trans hi
  exact ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, hf⟩

end ActualRawIdealLabels
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

section ActualRawCornerSteps
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (ha : P.area D ≠ ⊤)
    {n : ℕ} (V : Fin n → 𝕔𝔻) (hV : Function.Injective V)
    (hnext : ∀ i, finRotate n i ≠ i) (E : Fin n ≃ FuchsianPolygonSides P D)
    (hside : ∀ i, fuchsianSideClosedModel (E i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (V i) (V (finRotate n i)))
    (ρ : Equiv.Perm (Fin n)) (hρ : Function.Involutive ρ)
    (hleft : ∀ a, (P.compactifiedAction (fuchsianSideElement hD (E a))⁻¹).closedMap
      (V a) = V (finRotate n (ρ a)))
    (hright : ∀ a, (P.compactifiedAction (fuchsianSideElement hD (E a))⁻¹).closedMap
      (V (finRotate n a)) = V (ρ a))
    (J : PolygonalCircle)
    (hc : J.carrier = _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      (⋃ v : OriginalRefinedSide hD, v.carrier))
    (hv : ∀ p, J.IsVertexPoint p ↔ p ∈ _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD)
    (e : ZMod J.n ≃ OriginalRefinedSide hD) (hs : ∀ a, J.edgeSegment a = (e a).planeCarrier)
include E hside hV hnext hρ hleft hright ha hc hs

/-- One genuine raw ideal-corner identification is exactly a forward or
backward step of the unchanged original natural vertex permutation. -/
theorem cofinite_raw_ideal_corner_step (k l : ZMod J.n)
    (hkl : originalRawCornerStep J e k l) (i : Fin n)
    (hi : ‖(V i : ℂ)‖ = 1) (hik : V i = originalCyclicVertex hD J hv k) :
    ∃ j : Fin n, V j = originalCyclicVertex hD J hv l ∧
      (j = finRotate n (ρ i) ∨ i = finRotate n (ρ j)) := by
  obtain ⟨a, hmem, hact⟩ : ∃ a : ZMod J.n,
      originalCyclicVertex hD J hv k ∈ (e a).carrier ∧
      (P.compactifiedAction (fuchsianSideElement hD (e a).val.1)⁻¹).closedMap
        (originalCyclicVertex hD J hv k) = originalCyclicVertex hD J hv l := by
    obtain ⟨a, hkl | hkl⟩ := hkl
    · obtain ⟨hk, hl⟩ := hkl
      refine ⟨a, ?_, ?_⟩
      · rw [hk]
        exact (originalCyclicVertex_mem_side_iff hD J hv e hs a a).mpr (Or.inl rfl)
      · rw [hk, hl]
        exact (originalCyclicPairIndex_endpoint_reverse hD ha J hc hv e hs a).1
    · obtain ⟨hk, hl⟩ := hkl
      refine ⟨a, ?_, ?_⟩
      · rw [hk]
        exact (originalCyclicVertex_mem_side_iff hD J hv e hs (a + 1) a).mpr (Or.inr rfl)
      · rw [hk, hl]
        exact (originalCyclicPairIndex_endpoint_reverse hD ha J hc hv e hs a).2
  let b : Fin n := E.symm (e a).val.1
  have hEb : E b = (e a).val.1 := E.apply_symm_apply _
  have hmemQ : V i ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (V b) (V (finRotate n b)) := by
    rw [← hside, hEb, hik]
    exact (e a).carrier_subset_original hmem
  have hpoint := original_segment_ideal_eq_endpoint (V b) (V (finRotate n b))
    (V i) (hV.ne (hnext b).symm) hmemQ hi
  have hact' : (P.compactifiedAction (fuchsianSideElement hD (E b))⁻¹).closedMap
      (V i) = originalCyclicVertex hD J hv l := by
    rw [hEb, hik]
    exact hact
  rcases hpoint with hpoint | hpoint
  · have hib : i = b := hV hpoint
    subst i
    exact ⟨finRotate n (ρ b), (hleft b).symm.trans hact', Or.inl rfl⟩
  · have hib : i = finRotate n b := hV hpoint
    subst i
    refine ⟨ρ b, (hright b).symm.trans hact', Or.inr ?_⟩
    rw [hρ]

omit hV hnext hρ hright in
/-- Each forward original ideal step is one actual refined raw corner
identification, even if an original side was split at a finite order-two center. -/
theorem cofinite_raw_ideal_corner_edge (i : Fin n)
    (k : ZMod J.n) (hik : V i = originalCyclicVertex hD J hv k) :
    ∃ l : ZMod J.n, originalRawCornerStep J e k l ∧
      V (finRotate n (ρ i)) = originalCyclicVertex hD J hv l := by
  have hmem : V i ∈ fuchsianSideClosedModel (E i) := by
    rw [hside, ← _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedModelSegmentParam]
    exact ⟨0, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelSegmentParam_zero _ _⟩
  obtain ⟨v, hvS, hvz⟩ := OriginalRefinedSide.exists_over_side hD (E i) (V i) hmem
  let a : ZMod J.n := e.symm v
  have hea : e a = v := e.apply_symm_apply _
  have hmemRaw : originalCyclicVertex hD J hv k ∈ (e a).carrier := by
    rw [hea, ← hik]
    exact hvz
  have hclosed : (P.compactifiedAction (fuchsianSideElement hD (e a).val.1)⁻¹).closedMap
      (originalCyclicVertex hD J hv k) = V (finRotate n (ρ i)) := by
    rw [hea, hvS, ← hik]
    exact hleft i
  rcases (originalCyclicVertex_mem_side_iff hD J hv e hs k a).mp hmemRaw with hk | hk
  · refine ⟨originalCyclicPairIndex J e a + 1, ⟨a, Or.inl ⟨hk, rfl⟩⟩, ?_⟩
    have hrev := (originalCyclicPairIndex_endpoint_reverse hD ha J hc hv e hs a).1
    rw [hk] at hclosed
    exact hclosed.symm.trans hrev
  · refine ⟨originalCyclicPairIndex J e a, ⟨a, Or.inr ⟨hk, rfl⟩⟩, ?_⟩
    have hrev := (originalCyclicPairIndex_endpoint_reverse hD ha J hc hv e hs a).2
    rw [hk] at hclosed
    exact hclosed.symm.trans hrev

/-- The whole genuine raw ideal relation is precisely the whole original
natural-step relation on actual vertex labels. Both directions use actual
original side identifications, retaining all original occurrences. -/
theorem cofinite_raw_ideal_corner_chain (i j : Fin n)
    (hi : ‖(V i : ℂ)‖ = 1) (hj : ‖(V j : ℂ)‖ = 1)
    (k l : ZMod J.n) (hik : V i = originalCyclicVertex hD J hv k)
    (hjl : V j = originalCyclicVertex hD J hv l) :
    Relation.EqvGen (originalRawCornerStep J e) k l ↔
      Relation.EqvGen (fun a b : Fin n => b = finRotate n (ρ a)) i j := by
  let τ : Fin n → Fin n := fun a => finRotate n (ρ a)
  let R : Fin n → Fin n → Prop := fun a b => b = τ a
  let Z : ZMod J.n → 𝕔𝔻 := originalCyclicVertex hD J hv
  obtain ⟨L, hL⟩ := cofinite_raw_ideal_vertex_labels hD V hV hnext E hside J hv
  have hZinj : Function.Injective Z := originalCyclicVertex_injective hD J hv
  have hRawIdeal {a b : ZMod J.n} (hab : Relation.EqvGen (originalRawCornerStep J e) a b)
      (ha' : ‖(Z a : ℂ)‖ = 1) : ‖(Z b : ℂ)‖ = 1 := by
    have hf := originalRawCorner_finite_iff_rawChain hD ha J hc hv e hs hab
    apply le_antisymm (Z b).norm_le_one
    apply le_of_not_gt
    intro hb
    have ha'' := hf.mpr hb
    rw [ha'] at ha''
    exact (lt_irrefl (1 : ℝ)) ha''
  have hTauIdeal {a b : Fin n} (hab : Relation.EqvGen R a b) :
      ‖(V a : ℂ)‖ = 1 ↔ ‖(V b : ℂ)‖ = 1 := by
    induction hab with
    | rel a b hab =>
      change b = τ a at hab
      subst b
      rw [← hleft a]
      exact ((P.compactifiedAction (fuchsianSideElement hD (E a))⁻¹).ideal_iff (V a)).symm
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hF {a b : ZMod J.n} (hab : Relation.EqvGen (originalRawCornerStep J e) a b) :
      ∀ u v : Fin n, ‖(V u : ℂ)‖ = 1 → ‖(V v : ℂ)‖ = 1 →
        V u = Z a → V v = Z b → Relation.EqvGen R u v := by
    induction hab with
    | rel a b hab =>
      intro u v hu _hv hua hvb
      obtain ⟨v', hv', hstep⟩ := cofinite_raw_ideal_corner_step
        hD ha V hV hnext E hside ρ hρ hleft hright J hc hv e hs a b hab u hu hua
      have heq : v' = v := hV (hv'.trans hvb.symm)
      subst v'
      rcases hstep with hstep | hstep
      · exact Relation.EqvGen.rel _ _ hstep
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hstep)
    | refl a =>
      intro u v _hu _hv hua hva
      exact (hV (hua.trans hva.symm)) ▸ Relation.EqvGen.refl u
    | symm a b _ ih =>
      intro u v hu hv hua hvb
      exact Relation.EqvGen.symm _ _ (ih v u hv hu hvb hua)
    | trans a b c hab _hbc ih₁ ih₂ =>
      intro u v hu hv hua hvc
      have hb : ‖(Z b : ℂ)‖ = 1 := hRawIdeal hab (hua ▸ hu)
      let b' := L.symm ⟨b, hb⟩
      have hb' : V b'.val = Z b := by
        have h := hL b'
        rw [L.apply_symm_apply] at h
        exact h.symm
      exact Relation.EqvGen.trans _ _ _ (ih₁ u b'.val hu b'.property hua hb')
        (ih₂ b'.val v b'.property hv hb' hvc)
  have hB {a b : Fin n} (hab : Relation.EqvGen R a b) :
      ∀ ha' : ‖(V a : ℂ)‖ = 1, ∀ hb' : ‖(V b : ℂ)‖ = 1,
      ∀ u v : ZMod J.n, V a = Z u → V b = Z v →
        Relation.EqvGen (originalRawCornerStep J e) u v := by
    induction hab with
    | rel a b hab =>
      intro _ha' _hb' u v hau hbv
      change b = τ a at hab
      subst b
      obtain ⟨v', hstep, hv'⟩ := cofinite_raw_ideal_corner_edge
        (hD := hD) (ha := ha) (V := V) (E := E) (hside := hside) (ρ := ρ) (hleft := hleft)
        (J := J) (hc := hc) (hv := hv) (e := e) (hs := hs) a u hau
      have heq : v' = v := hZinj (hv'.symm.trans hbv)
      subst v'
      exact Relation.EqvGen.rel _ _ hstep
    | refl a =>
      intro _ha' _hb' u v hau hav
      exact (hZinj (hau.symm.trans hav)) ▸ Relation.EqvGen.refl u
    | symm a b _ ih =>
      intro ha' hb' u v hau hbv
      exact Relation.EqvGen.symm _ _ (ih hb' ha' v u hbv hau)
    | trans a b c hab _hbc ih₁ ih₂ =>
      intro ha' hc' u v hau hcv
      have hb' := (hTauIdeal hab).mp ha'
      let b' := L ⟨b, hb'⟩
      have hb : V b = Z b'.val := (hL ⟨b, hb'⟩).symm
      exact Relation.EqvGen.trans _ _ _ (ih₁ ha' hb' u b'.val hau hb)
        (ih₂ hb' hc' b'.val v hb hcv)
  exact ⟨fun h => hF h i j hi hj hik hjl, fun h => hB h hi hj k l hik hjl⟩

end ActualRawCornerSteps
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

section ActualRawZeroClasses
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (ha : P.area D ≠ ⊤)
    {n : ℕ} (V : Fin n → 𝕔𝔻) (hV : Function.Injective V) (hnext : ∀ i, finRotate n i ≠ i)
    (E : Fin n ≃ FuchsianPolygonSides P D)
    (hside : ∀ i, fuchsianSideClosedModel (E i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (V i) (V (finRotate n i)))
    (ρ : Equiv.Perm (Fin n)) (hρ : Function.Involutive ρ)
    (hleft : ∀ a, (P.compactifiedAction (fuchsianSideElement hD (E a))⁻¹).closedMap
      (V a) = V (finRotate n (ρ a)))
    (hright : ∀ a, (P.compactifiedAction (fuchsianSideElement hD (E a))⁻¹).closedMap
      (V (finRotate n a)) = V (ρ a))
    (J : PolygonalCircle)
    (hc : J.carrier = _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      (⋃ v : OriginalRefinedSide hD, v.carrier))
    (hv : ∀ p, J.IsVertexPoint p ↔ p ∈ _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD)
    (e : ZMod J.n ≃ OriginalRefinedSide hD) (hs : ∀ a, J.edgeSegment a = (e a).planeCarrier)
include E hside hρ hleft hright

/-- The actual raw zero-weight corner classes correspond exactly to the
original ideal-label natural classes, with each individual vertex label kept.
Finite self-side subdivisions are removed by actual ideality, not by an
assumed cyclic-order or group-orbit classification. -/
def cofinite_raw_zero_corner_classes_equiv :
    {q : Quotient (originalRawCornerSetoid J e) //
      originalRawCornerClassWeight hD ha J hc hv e hs q = 0} ≃
      Quotient ((Relation.EqvGen.setoid
        (fun a b : Fin n => b = finRotate n (ρ a))).comap
          (Subtype.val : {i : Fin n // ‖(V i : ℂ)‖ = 1} → Fin n)) := by
  let Z : ZMod J.n → 𝕔𝔻 := originalCyclicVertex hD J hv
  let I := {i : Fin n // ‖(V i : ℂ)‖ = 1}
  let K := {k : ZMod J.n // ‖(Z k : ℂ)‖ = 1}
  let Rraw : Setoid K := (originalRawCornerSetoid J e).comap Subtype.val
  let Ractual : Setoid I := (Relation.EqvGen.setoid
    (fun a b : Fin n => b = finRotate n (ρ a))).comap Subtype.val
  have hweight (k : ZMod J.n) : ‖(Z k : ℂ)‖ = 1 ↔
      originalRawCornerClassWeight hD ha J hc hv e hs (Quotient.mk _ k) = 0 := by
    rw [originalRawCornerClassWeight_zero_iff_ideal]
    let q : Quotient (originalRawCornerSetoid J e) := Quotient.mk _ k
    have hrel : Relation.EqvGen (originalRawCornerStep J e) q.out k :=
      Quotient.exact (Quotient.out_eq q)
    have hfinite := originalRawCorner_finite_iff_rawChain hD ha J hc hv e hs hrel
    constructor
    · intro hk
      apply le_antisymm (Z q.out).norm_le_one
      apply le_of_not_gt
      intro hq
      have hk' := hfinite.mp hq
      rw [hk] at hk'
      exact (lt_irrefl (1 : ℝ)) hk'
    · intro hq
      apply le_antisymm (Z k).norm_le_one
      apply le_of_not_gt
      intro hk
      have hq' := hfinite.mpr hk
      rw [hq] at hq'
      exact (lt_irrefl (1 : ℝ)) hq'
  let A : {q : Quotient (originalRawCornerSetoid J e) //
      originalRawCornerClassWeight hD ha J hc hv e hs q = 0} ≃ Quotient Rraw :=
    Equiv.subtypeQuotientEquivQuotientSubtype (fun k => ‖(Z k : ℂ)‖ = 1)
      (fun q => originalRawCornerClassWeight hD ha J hc hv e hs q = 0)
      hweight (fun _ _ => Iff.rfl)
  let L := Classical.choose (cofinite_raw_ideal_vertex_labels hD V hV hnext E hside J hv)
  have hL := Classical.choose_spec (cofinite_raw_ideal_vertex_labels hD V hV hnext E hside J hv)
  let B : Quotient Rraw ≃ Quotient Ractual := Quotient.congr L.symm (by
    intro a b
    have ha' : V (L.symm a).val = Z a.val := by
      have h := hL (L.symm a)
      rw [L.apply_symm_apply] at h
      exact h.symm
    have hb' : V (L.symm b).val = Z b.val := by
      have h := hL (L.symm b)
      rw [L.apply_symm_apply] at h
      exact h.symm
    exact cofinite_raw_ideal_corner_chain hD ha V hV hnext E hside ρ hρ hleft hright J hc hv e hs
      (L.symm a).val (L.symm b).val (L.symm a).property (L.symm b).property a.val b.val ha' hb')
  exact A.trans B

end ActualRawZeroClasses
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual whole-disc conjugation has its genuine closed hyperbolic extension. -/
def cofiniteRawDiscConjugation {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry := by
  let Q := P.conjugateData q hq
  let f := P.conjugateCoordinate q hq
  let F : Complex.UnitDisc → Complex.UnitDisc :=
    fun z => Q.finiteCoordinate (f (P.finiteCoordinate.symm z))
  have hF : ∀ z w, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (F z) (F w) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z w := by
    let cofiniteRawConjugationMetric : MetricSpace Complex.UnitDisc := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
    have hiso : Isometry F := P.conjugateCoordinate_isometry q hq
    intro z w
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using hiso.dist_eq z w
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.ofPathIsometry F hF

/-- The closed extension agrees with the actual original finite-point conjugation. -/
theorem cofiniteRawDiscConjugation_finite {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (x : P.domain.carrier) :
    (cofiniteRawDiscConjugation P q hq).closedMap
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ((P.conjugateData q hq).finiteCoordinate
        (P.conjugateCoordinate q hq x)) := by
  calc
    _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ((cofiniteRawDiscConjugation P q hq).finiteMap
        (P.finiteCoordinate x)) :=
      (cofiniteRawDiscConjugation P q hq).finite_commutes _
    _ = _ := by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ((P.conjugateData q hq).finiteCoordinate
        (P.conjugateCoordinate q hq (P.finiteCoordinate.symm (P.finiteCoordinate x)))) = _
      rw [P.finiteCoordinate.symm_apply_apply]

/-- Actual ideal status is unchanged by the genuine whole-disc conjugation. -/
theorem cofiniteRawDiscConjugation_ideal_iff {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (p : Complex.UnitClosedDisc) :
    ‖((cofiniteRawDiscConjugation P q hq).closedMap p : ℂ)‖ = 1 ↔ ‖(p : ℂ)‖ = 1 :=
  (cofiniteRawDiscConjugation P q hq).ideal_iff p

/-- The genuine closed extension intertwines the unchanged original group with its actual conjugate, including at every ideal endpoint. -/
theorem cofiniteRawDiscConjugation_equivariant {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (g : H)
    (p : Complex.UnitClosedDisc) :
    (cofiniteRawDiscConjugation P q hq).closedMap ((P.compactifiedAction g).closedMap p) =
      ((P.conjugateData q hq).compactifiedAction
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g)).closedMap
          ((cofiniteRawDiscConjugation P q hq).closedMap p) := by
  let cofiniteRawConjugationT2 : T2Space Complex.UnitClosedDisc :=
    Complex.UnitClosedDisc.isEmbedding_coe.t2Space
  let Q := P.conjugateData q hq
  let C := cofiniteRawDiscConjugation P q hq
  let E := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have he : C.closedMap ∘ (P.compactifiedAction g).closedMap =
      (Q.compactifiedAction (E g)).closedMap ∘ C.closedMap := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.denseRange_discToClosedModel.equalizer
      (C.closedMap.continuous.comp (P.compactifiedAction g).closedMap.continuous)
      ((Q.compactifiedAction (E g)).closedMap.continuous.comp C.closedMap.continuous)
    funext z
    let x := P.finiteCoordinate.symm z
    have hx : P.finiteCoordinate x = z := P.finiteCoordinate.apply_symm_apply z
    change C.closedMap ((P.compactifiedAction g).closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)) =
      (Q.compactifiedAction (E g)).closedMap (C.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z))
    rw [← hx, P.compactifiedAction_finite]
    rw [cofiniteRawDiscConjugation_finite, cofiniteRawDiscConjugation_finite,
      Q.compactifiedAction_finite]
    rw [P.conjugateCoordinate_equivariant]
  exact congrFun he p

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped Pointwise

/-- Whole-disc conjugation identifies every actual original side, including self-paired sides, by its true group element. -/
theorem cofiniteRawDiscSideConjugation_exists {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    ∃ e : FuchsianPolygonSides P D ≃
        FuchsianPolygonSides (P.conjugateData q hq) (P.conjugateCoordinate q hq '' D),
      ∀ s, fuchsianSideElement (P.conjugate_polygon_image q hq hD) (e s) =
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H (fuchsianSideElement hD s) := by
  classical
  let Q := P.conjugateData q hq
  let f := P.conjugateCoordinate q hq
  let E := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  let hQ := P.conjugate_polygon_image q hq hD
  have hmap (s : FuchsianPolygonSides P D) :
      ∃ t : FuchsianPolygonSides Q (f '' D),
        fuchsianSideElement hQ t = E (fuchsianSideElement hD s) := by
    obtain ⟨_, t, ht⟩ := equivariant_fuchsian_side_element_image P Q E f
      (P.conjugateCoordinate_equivariant q hq) (P.conjugateCoordinate_area_map q hq)
      (P.conjugateCoordinate_isometry q hq) hD s
    exact ⟨t, ht⟩
  choose φ hφ using hmap
  have hinj : Function.Injective φ := by
    intro s t hst
    apply fuchsianSideElement_injective hD
    apply E.injective
    rw [← hφ s, ← hφ t, hst]
  have hsurj : Function.Surjective φ := by
    intro t
    have hp := equivariant_fuchsian_side_element_preimage P Q E f
      (P.conjugateCoordinate_equivariant q hq) (P.conjugateCoordinate_area_map q hq)
      (P.conjugateCoordinate_isometry q hq) hQ t
    have hset : f ⁻¹' (f '' D) = D := f.injective.preimage_image D
    rw [hset] at hp
    obtain ⟨_, s, hs⟩ := hp
    refine ⟨s, ?_⟩
    apply fuchsianSideElement_injective hQ
    rw [hφ s, hs, E.apply_symm_apply]
  exact ⟨Equiv.ofBijective φ ⟨hinj, hsurj⟩, hφ⟩

/-- The actual original-side equivalence determined by the genuine whole-disc conjugation. -/
def cofiniteRawDiscSideConjugation {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    FuchsianPolygonSides P D ≃
      FuchsianPolygonSides (P.conjugateData q hq) (P.conjugateCoordinate q hq '' D) :=
  Classical.choose (cofiniteRawDiscSideConjugation_exists P q hq hD)

/-- Each transported side retains precisely the conjugate of its actual original group element. -/
theorem cofiniteRawDiscSideConjugation_element {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (s : FuchsianPolygonSides P D) :
    fuchsianSideElement (P.conjugate_polygon_image q hq hD)
        (cofiniteRawDiscSideConjugation P q hq hD s) =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H (fuchsianSideElement hD s) :=
  Classical.choose_spec (cofiniteRawDiscSideConjugation_exists P q hq hD) s

/-- The transported side is the image of the entire actual original finite carrier. -/
theorem cofiniteRawDiscSideConjugation_carrier {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (s : FuchsianPolygonSides P D) :
    P.conjugateCoordinate q hq '' s.val =
      (cofiniteRawDiscSideConjugation P q hq hD s).val := by
  let Q := P.conjugateData q hq
  let f := P.conjugateCoordinate q hq
  let E := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  let hQ := P.conjugate_polygon_image q hq hD
  let g := fuchsianSideElement hD s
  have htile : f '' fuchsianDomainTile P D g =
      fuchsianDomainTile Q (f '' D) (E g) := by
    change f '' (g • closure D) = E g • closure (f '' D)
    rw [← f.image_closure]
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨f z, ⟨z, hz, rfl⟩, (P.conjugateCoordinate_equivariant q hq g z).symm⟩
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨g • z, ⟨z, hz, rfl⟩, P.conjugateCoordinate_equivariant q hq g z⟩
  rw [(fuchsianSideElement_spec hD s).2,
    (fuchsianSideElement_spec hQ (cofiniteRawDiscSideConjugation P q hq hD s)).2,
    cofiniteRawDiscSideConjugation_element]
  change f '' (closure D ∩ fuchsianDomainTile P D g) =
    closure (f '' D) ∩ fuchsianDomainTile Q (f '' D) (E g)
  rw [image_inter f.injective, f.image_closure, htile]

/-- Genuine whole-disc conjugation carries the full finite-or-ideal closed original side onto its exact actual transported side. -/
theorem cofiniteRawDiscSideConjugation_closed_carrier {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (s : FuchsianPolygonSides P D) :
    (cofiniteRawDiscConjugation P q hq).closedMap '' fuchsianSideClosedModel s =
      fuchsianSideClosedModel (cofiniteRawDiscSideConjugation P q hq hD s) := by
  let C := cofiniteRawDiscConjugation P q hq
  let Q := P.conjugateData q hq
  let f := P.conjugateCoordinate q hq
  change C.closedMap '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' s.val) =
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (Q.finiteCoordinate ''
      (cofiniteRawDiscSideConjugation P q hq hD s).val)
  rw [← cofiniteRawDiscSideConjugation_carrier P q hq hD s]
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure, C.closedMap.image_closure, image_image]
  apply congrArg closure
  apply image_congr
  intro x _hx
  exact cofiniteRawDiscConjugation_finite P q hq x

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Filter
  Topology
  MeasureTheory
open LeanEval.Topology.ClassificationOfSurfaces.Moise
local instance rawCuspSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance rawCuspSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- All actual cusp classes of the unchanged original disc group are exactly
the actual ideal natural-corner classes. The geometric normalizer is carried
through the full closed action; it is never assumed to be the identity. -/
theorem cofinite_raw_ideal_cusp_classes_equiv {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D ≠ ⊤)
    {n : ℕ} (V : Fin n → 𝕔𝔻) (hV : Function.Injective V) (hnext : ∀ i, finRotate n i ≠ i)
    (E : Fin n ≃ FuchsianPolygonSides P D)
    (hside : ∀ i, fuchsianSideClosedModel (E i) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (V i) (V (finRotate n i)))
    (ρ : Equiv.Perm (Fin n)) (hρ : Function.Involutive ρ)
    (hleft : ∀ a, (P.compactifiedAction (fuchsianSideElement hD (E a))⁻¹).closedMap
      (V a) = V (finRotate n (ρ a)))
    (hright : ∀ a, (P.compactifiedAction (fuchsianSideElement hD (E a))⁻¹).closedMap
      (V (finRotate n a)) = V (ρ a))
    (hparV : ∀ i, ‖(V i : ℂ)‖ = 1 → ∃ g : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∧
      (P.compactifiedAction g).closedMap (V i) = V i) :
    Nonempty (Quotient ((Relation.EqvGen.setoid
        (fun a b : Fin n => b = finRotate n (ρ a))).comap
          (Subtype.val : {i : Fin n // ‖(V i : ℂ)‖ = 1} → Fin n)) ≃
      FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) := by
  let D₀ := P.asFuchsianDisc
  let q := geometricDiscNormalizer D₀
  have hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := geometricDiscNormalizer_image D₀
  let PN := P.conjugateData q hq
  let f := P.conjugateCoordinate q hq
  let C := cofiniteRawDiscConjugation P q hq
  let EN := E.trans (cofiniteRawDiscSideConjugation P q hq hD)
  let VN : Fin n → 𝕔𝔻 := fun i => C.closedMap (V i)
  have hDN : IsConvexFuchsianPolygon (geometricDiscData D₀) (f '' D) :=
    P.conjugate_polygon_image q hq hD
  have harea : PN.area (f '' D) = P.area D := by
    rw [← P.conjugateCoordinate_area_map q hq, f.measurableEmbedding.map_apply,
      f.injective.preimage_image]
  have haN : (geometricDiscData D₀).area (f '' D) ≠ ⊤ := by
    change PN.area (f '' D) ≠ ⊤
    rw [harea]
    exact ha
  have hVN : Function.Injective VN := C.closedMap.injective.comp hV
  have hsideN (i : Fin n) : fuchsianSideClosedModel (EN i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (VN i) (VN (finRotate n i)) := by
    change fuchsianSideClosedModel (cofiniteRawDiscSideConjugation P q hq hD (E i)) = _
    rw [← cofiniteRawDiscSideConjugation_closed_carrier P q hq hD (E i), hside]
    exact C.image_closedModelDiscHSegment (V i) (V (finRotate n i))
  have hEndsN (a : Fin n) :
      (PN.compactifiedAction (fuchsianSideElement hDN (EN a))⁻¹).closedMap (VN a) = VN (finRotate n (ρ a)) ∧
      (PN.compactifiedAction (fuchsianSideElement hDN (EN a))⁻¹).closedMap (VN (finRotate n a)) = VN (ρ a) := by
    have he : (fuchsianSideElement hDN (EN a))⁻¹ =
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H (fuchsianSideElement hD (E a))⁻¹ := by
      change (fuchsianSideElement (P.conjugate_polygon_image q hq hD)
        (cofiniteRawDiscSideConjugation P q hq hD (E a)))⁻¹ = _
      rw [cofiniteRawDiscSideConjugation_element P q hq hD, map_inv]
    constructor
    · rw [he, ← cofiniteRawDiscConjugation_equivariant P q hq, hleft]
    · rw [he, ← cofiniteRawDiscConjugation_equivariant P q hq, hright]
  obtain ⟨J, e, hc, hv, hs⟩ := finite_area_original_cyclic_side_model hDN haN
  obtain ⟨m, S, hr, _hint⟩ := finite_area_polygon_actual_cyclic_model hDN haN
  have hpar : ∀ u : Circle, (u : ℂ) ∈ fuchsianPolygonIdealBoundary (geometricDiscData D₀) (f '' D) →
      ∃ g : geometricDiscGroup D₀, g ≠ 1 ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∧
        g.val.val ((u : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((u : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    intro u hu
    have hcoe : Topology.IsClosedEmbedding (fun p : 𝕔𝔻 => (p : ℂ)) :=
      Complex.UnitClosedDisc.isEmbedding_coe.continuous.isClosedEmbedding
        Complex.UnitClosedDisc.isEmbedding_coe.injective
    have hclImage : (fun p : 𝕔𝔻 => (p : ℂ)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure
        (PN.finiteCoordinate '' (f '' D)) =
        closure ((fun x => (PN.finiteCoordinate x : ℂ)) '' (f '' D)) := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure, ← hcoe.closure_image_eq, image_image, image_image]
      rfl
    have hcl : (u : ℂ) ∈ (fun p : 𝕔𝔻 => (p : ℂ)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure
        (PN.finiteCoordinate '' (f '' D)) := by
      rw [hclImage]
      exact ((mem_fuchsianPolygonIdealBoundary PN (f '' D) (u : ℂ)).mp hu).1
    obtain ⟨p, hp, hpu⟩ := hcl
    change (p : ℂ) = (u : ℂ) at hpu
    have hpn : ‖(p : ℂ)‖ = 1 := by rw [hpu]; exact Circle.norm_coe u
    obtain ⟨k, hk⟩ := originalIdealClosedModel_is_rawVertex hDN haN J hv e hs p hp hpn
    have hpE : p ∈ originalRefinedEndpointSet hDN := by
      rw [← hk]
      exact originalCyclicVertex_mem_endpointSet hDN J hv k
    obtain ⟨i, hip⟩ := (cofinite_raw_ideal_endpoint_iff hDN VN hVN hnext EN hsideN p hpn).mpr hpE
    have hiN : ‖(VN i : ℂ)‖ = 1 := by rw [hip]; exact hpn
    have hi : ‖(V i : ℂ)‖ = 1 := (C.ideal_iff (V i)).mp hiN
    obtain ⟨g, hgpar, hgfix⟩ := hparV i hi
    let gN := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g
    have hgNpar : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic gN.val :=
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q, rfl⟩)).mp hgpar
    have hgNfix : (PN.compactifiedAction gN).closedMap p = p := by
      rw [← hip]
      rw [← cofiniteRawDiscConjugation_equivariant P q hq, hgfix]
    refine ⟨gN, fun he => hgNpar.1 (congrArg Subtype.val he), hgNpar, ?_⟩
    have h := PN.compactifiedAction_sphere gN p
    rw [hgNfix] at h
    change ((p : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = gN.val.val ((p : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at h
    rw [hpu] at h
    exact h.symm
  let A := cofinite_raw_zero_corner_classes_equiv hDN haN VN hVN hnext EN hsideN ρ hρ
    (fun a => (hEndsN a).1) (fun a => (hEndsN a).2) J hc hv e hs
  let B := originalRawIdealCuspEquiv D₀ hDN haN J hc hv e hs S hr hpar
  let L : {i : Fin n // ‖(V i : ℂ)‖ = 1} ≃ {i : Fin n // ‖(VN i : ℂ)‖ = 1} :=
    Equiv.subtypeEquivRight (fun i => (C.ideal_iff (V i)).symm)
  let R₀ := (Relation.EqvGen.setoid (fun a b : Fin n => b = finRotate n (ρ a))).comap
    (Subtype.val : {i : Fin n // ‖(V i : ℂ)‖ = 1} → Fin n)
  let R₁ := (Relation.EqvGen.setoid (fun a b : Fin n => b = finRotate n (ρ a))).comap
    (Subtype.val : {i : Fin n // ‖(VN i : ℂ)‖ = 1} → Fin n)
  let T : Quotient R₀ ≃ Quotient R₁ := Quotient.congr L (fun _ _ => Iff.rfl)
  exact ⟨T.trans (A.symm.trans B)⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

section MixedIdealFixers
variable {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (ρ : Equiv.Perm (Fin n))
    (hρ : Function.Involutive ρ) (hθρ : ∀ i, θ i = θ (finRotate n (ρ i)))
    (hPeriod : ∀ i : Fin n, 0 < θ i → ∃ N : ℕ,
      3 ≤ N ∧ ((ρ.trans (finRotate n))^[N]) i = i ∧ θ i = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
include hPeriod

local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "S₀" => cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
local notation "P₀" => cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "E₀" => MulEquiv.trans (cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ)
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
    (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))

/-- The actual original Cayley-group action of every real-SL member agrees on the entire compactified disc with its genuine native closed action. -/
theorem cofiniteMixedTangential_realSL_closedAction
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ (S₀).Generated)
    (p : Complex.UnitClosedDisc) :
    ((P₀).cayleyData.compactifiedAction (E₀ ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hA⟩)).closedMap p =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry A).closedMap p := by
  let cofiniteMixedFixerT2 : T2Space Complex.UnitClosedDisc :=
    Complex.UnitClosedDisc.isEmbedding_coe.t2Space
  let g : (S₀).Generated := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hA⟩
  have he : (fun r : Complex.UnitClosedDisc =>
      ((P₀).cayleyData.compactifiedAction (E₀ g)).closedMap r) =
      fun r : Complex.UnitClosedDisc => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry A).closedMap r := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.denseRange_discToClosedModel.equalizer
      ((P₀).cayleyData.compactifiedAction (E₀ g)).closedMap.continuous
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry A).closedMap.continuous
    funext z
    change ((P₀).cayleyData.compactifiedAction (E₀ g)).closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry A).closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    let x := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z
    have hcoord : (P₀).cayleyData.finiteCoordinate (f₀ x) = z := by
      rw [HalfPlaneFuchsianGroup.cayleyCoordinate_finite]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane z
    calc
      _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ((P₀).cayleyData.finiteCoordinate (E₀ g • f₀ x)) := by
        rw [← hcoord, UnitDiscFuchsianGroup.compactifiedAction_finite]
      _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (g.val x)) := by
        rw [← cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod g x,
          HalfPlaneFuchsianGroup.cayleyCoordinate_finite]
      _ = _ := by
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes]
        rfl
  exact congrFun he p

/-- Every actual zero-angle label has a nonidentity parabolic fixer in the unchanged entire Cayley group, fixing its literal original ideal vertex. -/
theorem cofiniteMixedTangential_zero_parabolic_fixer (i : Fin n) (hi : θ i = 0) :
    ∃ g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
        (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ),
      g ≠ 1 ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∧
        ((P₀).cayleyData.compactifiedAction g).closedMap ((Q₀).vertices i) =
          (Q₀).vertices i := by
  obtain ⟨A, hA, hpar, hfix⟩ :=
    cofiniteTangential_zero_parabolic_fixer θ d hθ hd hb ρ hρ hθρ i hi
  let g := E₀ ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hA⟩
  have hmatrix : g.val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A * _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius * nativeConformalSubgroupMobiusHom (S₀).Generated
      (cofiniteMixedTangentialGenerated_conformal θ d hθ hd hb ρ hρ hθρ)
        ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hA⟩ * _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ = _
    rw [nativeConformalSubgroupMobiusHom_matrix]
  have hpar' : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val := by
    rw [hmatrix]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius, rfl⟩)).mp hpar
  refine ⟨g, ?_, hpar', ?_⟩
  · intro hg
    exact hpar'.1 (congrArg Subtype.val hg)
  · rw [cofiniteMixedTangential_realSL_closedAction θ d hθ hd hb ρ hρ hθρ hPeriod A hA]
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm.injective
    apply Subtype.ext
    rw [cofiniteSL_closed_halfPlane_value]
    exact hfix

end MixedIdealFixers
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set

section ActualMixedCuspClasses
variable {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi)
    (ρ : Equiv.Perm (Fin n)) (hρ : Function.Involutive ρ)
    (hθρ : ∀ i, θ i = θ (finRotate n (ρ i)))
    (hPeriod : ∀ i : Fin n, 0 < θ i → ∃ N : ℕ, 3 ≤ N ∧
      ((ρ.trans (finRotate n))^[N]) i = i ∧ θ i = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "P₀" => cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "hD₀" => cofiniteMixedTangential_projective_disc_convex θ d hθ hd hb ρ hρ hθρ hPeriod

/-- Every actual cusp class of the full constructed original group is
exactly one zero-angle natural vertex class of its original polygon. -/
theorem cofiniteMixedTangential_ideal_cusp_classes_equiv :
    Nonempty (Quotient ((Relation.EqvGen.setoid
        (fun a b : Fin n => b = finRotate n (ρ a))).comap
          (Subtype.val : {i : Fin n // ‖((Q₀).vertices i : ℂ)‖ = 1} → Fin n)) ≃
      FuchsianCyclicConjugacyClasses (P₀).cayleyData.asFuchsianDisc .parabolic) := by
  apply cofinite_raw_ideal_cusp_classes_equiv (P₀).cayleyData hD₀
    (ne_of_lt (cofiniteMixedTangential_projective_disc_area_lt_top θ d hθ hd hb ρ hρ hθρ hPeriod))
    (Q₀).vertices (Q₀).vertices_injective (Q₀).next_ne_self
    (cofiniteMixedTangentialOriginalSideEquiv θ d hθ hd hb ρ hρ hθρ hPeriod)
    (fun a => cofiniteMixedTangentialOriginalSide_closedModel θ d hθ hd hb ρ hρ hθρ hPeriod a)
    ρ hρ
    (fun a => (cofiniteMixedTangentialOriginalSide_endpoints θ d hθ hd hb ρ hρ hθρ hPeriod a).1)
    (fun a => (cofiniteMixedTangentialOriginalSide_endpoints θ d hθ hd hb ρ hρ hθρ hPeriod a).2)
  intro i hi
  have hθi : θ i = 0 := (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_ideal_iff θ d hθ hd i).mp hi
  obtain ⟨g, _hne, hpar, hfix⟩ :=
    cofiniteMixedTangential_zero_parabolic_fixer θ d hθ hd hb ρ hρ hθρ hPeriod i hθi
  exact ⟨g, hpar, hfix⟩

end ActualMixedCuspClasses

/-- The prescribed zero-order marks, each with its own original list
occurrence, correspond to all actual cusp classes of the constructed group. -/
theorem cofiniteConstruction_mixed_cusp_classes_equiv (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hms : ∀ m ∈ ms, m = 0 ∨ 2 ≤ m) (hlast : last = 0 ∨ 2 ≤ last)
    (hdef : 0 < cofiniteConstructionDeficit g ms last) (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i => (cofiniteConstructionAngles g ms last)[i]) d = Real.pi) :
    let θ : Fin (cofiniteConstructionAngles g ms last).length → ℝ :=
      fun i => (cofiniteConstructionAngles g ms last)[i]
    let hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi :=
      fun i => cofiniteConstruction_angles_mem g ms last hms hlast hdef _ (List.getElem_mem i.isLt)
    let ρ := cofiniteConstructionPairing g ms last
    let hρ := cofiniteConstructionPairing_involutive g ms last
    let hθρ := cofiniteConstructionPairing_angle_profile g ms last
    let hPeriod : ∀ i, 0 < θ i → ∃ N : ℕ, 3 ≤ N ∧ ((ρ.trans (finRotate _))^[N]) i = i ∧
        θ i = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N := cofiniteConstruction_mixed_angular_periods g ms last hms hlast hdef
    let P := cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
    Nonempty (FuchsianCyclicConjugacyClasses P.cayleyData.asFuchsianDisc .parabolic ≃
      ({_u : Unit // last = 0} ⊕ {j : Fin ms.length // ms[j] = 0})) := by
  intro θ hθ ρ hρ hθρ hPeriod P
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  have hB : 2 ≤ 4 * g + ms.length := cofiniteConstruction_base_count g ms last hdef
  let R := (cofiniteConstructionCornerSetoid g ms last).comap
    (Subtype.val : {i : Fin (cofiniteConstructionAngles g ms last).length // ‖(Q.vertices i : ℂ)‖ = 1} → _)
  have hAngle (i : Fin (cofiniteConstructionAngles g ms last).length) :
      ‖(Q.vertices i : ℂ)‖ = 1 ↔
        cofiniteConstructionCornerQuotientAngle g ms last hB (Quotient.mk _ i) = 0 := by
    rw [cofiniteConstructionCornerQuotientAngle_mk]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_ideal_iff θ d hθ hd i
  let A : {q : Quotient (cofiniteConstructionCornerSetoid g ms last) //
      cofiniteConstructionCornerQuotientAngle g ms last hB q = 0} ≃ Quotient R :=
    Equiv.subtypeQuotientEquivQuotientSubtype (fun i => ‖(Q.vertices i : ℂ)‖ = 1)
      (fun q => cofiniteConstructionCornerQuotientAngle g ms last hB q = 0) hAngle (fun _ _ => Iff.rfl)
  obtain ⟨B⟩ := cofiniteMixedTangential_ideal_cusp_classes_equiv θ d hθ hd hb ρ hρ hθρ hPeriod
  let B' : Quotient R ≃ FuchsianCyclicConjugacyClasses P.cayleyData.asFuchsianDisc .parabolic := B
  exact ⟨B'.symm.trans (A.symm.trans (cofiniteConstructionZeroCornerClassesEquiv g ms last hB))⟩

/-- The complete actual cusp count retains the multiplicity of every
original zero-order occurrence, including a zero-order base mark. -/
theorem cofiniteConstruction_mixed_cusp_classes_card (g : ℕ) (ms : List ℕ) (last : ℕ)
    (hms : ∀ m ∈ ms, m = 0 ∨ 2 ≤ m) (hlast : last = 0 ∨ 2 ≤ last)
    (hdef : 0 < cofiniteConstructionDeficit g ms last) (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i => (cofiniteConstructionAngles g ms last)[i]) d = Real.pi) :
    let θ : Fin (cofiniteConstructionAngles g ms last).length → ℝ :=
      fun i => (cofiniteConstructionAngles g ms last)[i]
    let hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi :=
      fun i => cofiniteConstruction_angles_mem g ms last hms hlast hdef _ (List.getElem_mem i.isLt)
    let ρ := cofiniteConstructionPairing g ms last
    let hρ := cofiniteConstructionPairing_involutive g ms last
    let hθρ := cofiniteConstructionPairing_angle_profile g ms last
    let hPeriod : ∀ i, 0 < θ i → ∃ N : ℕ, 3 ≤ N ∧ ((ρ.trans (finRotate _))^[N]) i = i ∧
        θ i = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N := cofiniteConstruction_mixed_angular_periods g ms last hms hlast hdef
    let P := cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
    Nat.card (FuchsianCyclicConjugacyClasses P.cayleyData.asFuchsianDisc .parabolic) =
      (if last = 0 then 1 else 0) + ms.count 0 := by
  intro θ hθ ρ hρ hθρ hPeriod P
  obtain ⟨E⟩ := cofiniteConstruction_mixed_cusp_classes_equiv g ms last hms hlast hdef d hd hb
  rw [Nat.card_congr E, Nat.card_sum]
  have hUnit : Nat.card {_u : Unit // last = 0} = if last = 0 then 1 else 0 := by
    classical
    by_cases hl : last = 0 <;> simp [hl, Nat.card_eq_fintype_card]
  rw [hUnit]
  congr 1
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Fin.card_filter_univ_eq_vector_get_eq_count 0 ⟨ms, rfl⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology
open scoped Classical

/-- With the distinguished mark a cusp, every finite original corner is
one of the unchanged positive outer occurrences. -/
theorem cofiniteConstruction_cusped_finite_corner_labels (g:ℕ) (ms:List ℕ)
    (hms:∀m∈ms,m=0∨2≤m) (hdef:0<cofiniteConstructionDeficit g ms 0)
    (i:Fin (cofiniteConstructionAngles g ms 0).length)
    (hi:0<(cofiniteConstructionAngles g ms 0)[i]) :
    ∃j:{j:Fin ms.length//2<ms[j]},i=cofiniteConstructionOuterIndex g ms 0 ⟨j.val,by omega⟩ := by
  have hB:=cofiniteConstruction_base_count g ms 0 hdef
  obtain ⟨a,rfl⟩:=(cofiniteConstructionCornerLabelEquiv g ms 0 hB).surjective i
  cases a with
  | inl a=>
    rw [cofiniteConstructionCornerLabelEquiv_base,cofiniteConstructionBaseIndex_angle] at hi
    simp only [cofiniteConstructionBaseAngle,cofiniteConstructionConeAngle,Nat.cast_zero,div_zero,
      zero_div,lt_self_iff_false] at hi
  | inr j=>
    rw [cofiniteConstructionCornerLabelEquiv_outer] at hi ⊢
    have hm:2<ms[j.val]:=by
      change 2<ms[j.val.val]
      have hj2:ms[j.val.val]≠2:=j.property
      rcases hms _ (List.getElem_mem j.val.isLt) with hz|hm
      · rw [cofiniteConstructionOuterIndex_angle] at hi
        change 0<cofiniteConstructionConeAngle ms[j.val.val] at hi
        rw [hz] at hi
        simp [cofiniteConstructionConeAngle] at hi
      · omega
    exact ⟨⟨j.val,hm⟩,rfl⟩

/-- All zero reciprocals remain in the genuine physical area, while the
actual elliptic order list omits exactly the original cusp occurrences. -/
theorem cofiniteConstruction_positive_order_deficit (ms:List ℕ) :
    (((ms.filter (fun m=>m≠0)).map (fun m:ℕ=>(1:ℝ)-1/(m:ℝ))).sum)=
      (ms.length:ℝ)-(ms.count 0:ℝ)-(ms.map (fun m:ℕ=>(1:ℝ)/(m:ℝ))).sum := by
  induction ms with
  | nil=>simp
  | cons m ms ih=>
    by_cases hm:m=0
    · subst m
      rw [show (0::ms).filter (fun m:ℕ=>m≠0)=ms.filter (fun m:ℕ=>m≠0) by simp]
      simp only [List.map_cons,List.sum_cons,
        List.length_cons,List.count_cons_self,Nat.cast_add,Nat.cast_one,Nat.cast_zero,
        div_zero,zero_add]
      rw [ih]
      ring
    · rw [show (m::ms).filter (fun k:ℕ=>k≠0)=m::ms.filter (fun k:ℕ=>k≠0) by simp [hm]]
      simp only [List.map_cons,List.sum_cons,List.length_cons,
        List.count_cons_of_ne hm,Nat.cast_add,Nat.cast_one]
      rw [ih]
      ring

/-- The constructed physical angle defect is exactly the deficit of the
actual finite-order list together with all actual zero-order occurrences. -/
theorem cofiniteConstruction_cusp_signature_deficit (g:ℕ) (ms:List ℕ) :
    cofiniteConstructionDeficit g ms 0=
      2*(g:ℝ)-2+((1+ms.count 0:ℕ):ℝ)+
        ((ms.filter (fun m=>m≠0)).map (fun m:ℕ=>(1:ℝ)-1/(m:ℝ))).sum := by
  rw [cofiniteConstruction_positive_order_deficit]
  simp only [cofiniteConstructionDeficit,Nat.cast_zero,div_zero,add_zero,Nat.cast_add,Nat.cast_one]
  ring

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
open MeasureTheory
local instance cofiniteMixedSignatureSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance cofiniteMixedSignatureSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- The unchanged mixed fundamental domain has exactly the physical area
of the prescribed construction, including every zero-order occurrence. -/
theorem cofiniteConstruction_cusped_physical_area (g : ℕ) (ms : List ℕ)
    (hms : ∀ m ∈ ms, m = 0 ∨ 2 ≤ m) (hdef : 0 < cofiniteConstructionDeficit g ms 0)
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i => (cofiniteConstructionAngles g ms 0)[i]) d = Real.pi) :
    let θ : Fin (cofiniteConstructionAngles g ms 0).length → ℝ :=
      fun i => (cofiniteConstructionAngles g ms 0)[i]
    let hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi :=
      fun i => cofiniteConstruction_angles_mem g ms 0 hms (Or.inl rfl) hdef _ (List.getElem_mem i.isLt)
    let ρ := cofiniteConstructionPairing g ms 0
    let hρ := cofiniteConstructionPairing_involutive g ms 0
    let hθρ := cofiniteConstructionPairing_angle_profile g ms 0
    let hPeriod : ∀ i, 0 < θ i → ∃ N : ℕ, 3 ≤ N ∧ ((ρ.trans (finRotate _))^[N]) i = i ∧
        θ i = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N := cofiniteConstruction_mixed_angular_periods g ms 0 hms (Or.inl rfl) hdef
    let P := cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
    P.cayleyData.area (P.cayleyCoordinate '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹'
      _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb))) =
        ENNReal.ofReal (2 * Real.pi * cofiniteConstructionDeficit g ms 0) := by
  intro θ hθ ρ hρ hθρ hPeriod P
  rw [cofiniteMixedTangential_projective_disc_area_exact θ d hθ hd hb ρ hρ hθρ hPeriod]
  congr 1
  have hs : ∑ i : Fin (cofiniteConstructionAngles g ms 0).length, θ i =
      (cofiniteConstructionAngles g ms 0).sum := by
    change (∑ i : Fin (cofiniteConstructionAngles g ms 0).length,
      (cofiniteConstructionAngles g ms 0)[i.val]) = (cofiniteConstructionAngles g ms 0).sum
    rw [← List.sum_ofFn, List.ofFn_getElem]
  rw [hs]
  exact cofiniteConstruction_angles_defect g ms 0
    (lt_of_lt_of_le (by decide : 0 < 2) (cofiniteConstruction_base_count g ms 0 hdef))

/-- The genuine finite-area completion genus is forced by the actual
elliptic-order list, the already proved actual cusp classes, and physical area.
The remaining order-list premise is an internal input to the class-enumeration consumer. -/
theorem cofiniteConstruction_cusped_signature_of_actual_orders (g : ℕ) (ms : List ℕ)
    (hms : ∀ m ∈ ms, m = 0 ∨ 2 ≤ m) (hdef : 0 < cofiniteConstructionDeficit g ms 0)
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i => (cofiniteConstructionAngles g ms 0)[i]) d = Real.pi) :
    let θ : Fin (cofiniteConstructionAngles g ms 0).length → ℝ :=
      fun i => (cofiniteConstructionAngles g ms 0)[i]
    let hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi :=
      fun i => cofiniteConstruction_angles_mem g ms 0 hms (Or.inl rfl) hdef _ (List.getElem_mem i.isLt)
    let ρ := cofiniteConstructionPairing g ms 0
    let hρ := cofiniteConstructionPairing_involutive g ms 0
    let hθρ := cofiniteConstructionPairing_angle_profile g ms 0
    let hPeriod : ∀ i, 0 < θ i → ∃ N : ℕ, 3 ≤ N ∧ ((ρ.trans (finRotate _))^[N]) i = i ∧
        θ i = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N := cofiniteConstruction_mixed_angular_periods g ms 0 hms (Or.inl rfl) hdef
    let P := cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
    (∀ [Finite (FuchsianCyclicConjugacyClasses P.cayleyData.asFuchsianDisc .elliptic)],
      (ms.filter (fun m => m ≠ 0)).Perm (fuchsianEllipticOrderList P.cayleyData.asFuchsianDisc)) →
      HasCofiniteFuchsianSignature P.cayleyData.asFuchsianDisc
        g (ms.filter (fun m => m ≠ 0)) (1 + ms.count 0) := by
  intro θ hθ ρ hρ hθρ hPeriod P horders
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let D := P.cayleyCoordinate '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q)
  have hFD : IsFuchsianFundamentalDomain P.cayleyData D :=
    cofiniteMixedTangential_projective_disc_fundamental θ d hθ hd hb ρ hρ hθρ hPeriod
  have ha : P.cayleyData.area D ≠ ⊤ := by
    rw [cofiniteConstruction_cusped_physical_area g ms hms hdef d hd hb]
    exact ENNReal.ofReal_ne_top
  obtain ⟨s, hbnd, hSig, harea⟩ := finite_area_unitDisc_signature_area P.cayleyData D hFD ha
  let := hSig.ellipticClassesFinite
  have hperm : s.ellipticOrders.Perm (ms.filter (fun m => m ≠ 0)) :=
    hSig.ellipticOrders.trans horders.symm
  have hcusps : s.parabolicEnds = 1 + ms.count 0 := by
    apply hSig.cuspCount.trans
    simpa only [ite_true] using cofiniteConstruction_mixed_cusp_classes_card g ms 0 hms
      (Or.inl rfl) hdef d hd hb
  have hnonneg : 0 ≤ 2 * Real.pi * cofiniteConstructionDeficit g ms 0 := by positivity
  rw [cofiniteConstruction_cusped_physical_area g ms hms hdef d hd hb,
    ENNReal.toReal_ofReal hnonneg, cofiniteConstruction_cusp_signature_deficit g ms] at harea
  simp only [FuchsianSignature.deficit, hbnd, hcusps, Nat.cast_zero, add_zero] at harea
  rw [(hperm.map (fun m : ℕ => (1 : ℝ) - 1 / (m : ℝ))).sum_eq] at harea
  have hgenus : (s.genus : ℝ) = g := by nlinarith [Real.pi_pos]
  have hg : s.genus = g := by exact_mod_cast hgenus
  exact {
    ellipticClassesFinite := hSig.ellipticClassesFinite
    parabolicClassesFinite := hSig.parabolicClassesFinite
    compact := hSig.compact
    topologicalGenus := hg ▸ hSig.topologicalGenus
    ellipticOrders := hperm.symm.trans hSig.ellipticOrders
    cuspCount := hcusps ▸ hSig.cuspCount }

end LowDimensionalTopology.Geometry.Fuchsian


namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology

section MixedSelfCenters
variable {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi)
    (ρ : Equiv.Perm (Fin n)) (hρ : Function.Involutive ρ)
    (hθρ : ∀ i, θ i = θ (finRotate n (ρ i)))
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "S₀" => cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
local notation "w₀" => fun i : Fin n => _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))
include hθρ

/-- A genuine self-side contact point is not any original native vertex,
even when some original endpoints are ideal. -/
theorem cofiniteMixedTangential_self_foot_nonvertex (i : Fin n) (hi : ρ i = i) :
    w₀ i ∉ _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀ := by
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i))
  let A := cofiniteTangentPairingClosedIsometry θ d hθ hd hb i i
  have ha : θ i = θ (finRotate n i) := by simpa only [hi] using hθρ i
  have hfix : A.closedMap v = v := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes, cofiniteTangentPairingClosedIsometry_finite,
      cofiniteTangentPairingElement_self_foot, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  have hleft : v ≠ (Q₀).vertices i := by
    intro he
    have hm := cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i i ha
    change A.closedMap ((Q₀).vertices i) = (Q₀).vertices (finRotate n i) at hm
    rw [← he, hfix] at hm
    exact (Q₀).next_ne_self i ((Q₀).vertices_injective (he.symm.trans hm)).symm
  have hright : v ≠ (Q₀).vertices (finRotate n i) := by
    intro he
    have hm := cofiniteTangentPairingClosedIsometry_vertex_right θ d hθ hd hb i i ha.symm
    change A.closedMap ((Q₀).vertices (finRotate n i)) = (Q₀).vertices i at hm
    rw [← he, hfix] at hm
    exact (Q₀).next_ne_self i ((Q₀).vertices_injective (he.symm.trans hm))
  rintro ⟨j, hj⟩
  have hz : (Q₀).vertices j = v := by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] using hj
  have hlabels := cofiniteJordan_vertex_side_labels Q₀ j
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)) hz (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)
    (cofiniteTangential_foot_mem_side θ d hθ hd hb i)
  rcases hlabels with hin | hout
  · have hii := (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀).injective hin
    have hji : j = finRotate n i := by
      rw [hii]
      exact ((finRotate n).apply_symm_apply j).symm
    exact hright (hz.symm.trans (congrArg (Q₀).vertices hji))
  · have hii := (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀).injective hout
    exact hleft (hz.symm.trans (congrArg (Q₀).vertices hii.symm))

variable (hPeriod : ∀ i : Fin n, 0 < θ i → ∃ N : ℕ, 3 ≤ N ∧
  ((ρ.trans (finRotate n))^[N]) i = i ∧ θ i = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
include hPeriod
local notation "P₀" => cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => f₀ '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q₀)
local notation "E₀" => MulEquiv.trans (cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ)
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))
local notation "hD₀" => cofiniteMixedTangential_projective_disc_convex θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "s₀" => cofiniteMixedTangentialOriginalSide θ d hθ hd hb ρ hρ hθρ hPeriod

/-- Every actual original Fuchsian vertex is an unchanged native vertex
of the prescribed polygon, as forced by its two true incident sides. -/
theorem cofiniteMixedTangential_actual_vertex_native (x : ℍ)
    (hx : IsFuchsianPolygonVertex (P₀).cayleyData D₀ (f₀ x)) :
    x ∈ _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀ := by
  obtain ⟨U, V, hU, hV, hUV, hxU, hxV⟩ := (hD₀).vertex_exists_two_sides hx
  obtain ⟨i, hi⟩ := (cofiniteMixedTangentialOriginalSideEquiv θ d hθ hd hb ρ hρ hθρ hPeriod).surjective ⟨U, hU⟩
  obtain ⟨j, hj⟩ := (cofiniteMixedTangentialOriginalSideEquiv θ d hθ hd hb ρ hρ hθρ hPeriod).surjective ⟨V, hV⟩
  have hij : i ≠ j := by
    intro he
    apply hUV
    exact congrArg Subtype.val (hi.symm.trans ((congrArg
      (cofiniteMixedTangentialOriginalSideEquiv θ d hθ hd hb ρ hρ hθρ hPeriod) he).trans hj))
  have hxi : f₀ x ∈ (s₀ i).val := by
    change f₀ x ∈ ((cofiniteMixedTangentialOriginalSideEquiv θ d hθ hd hb ρ hρ hθρ hPeriod) i).val
    rw [hi]
    exact hxU
  have hxj : f₀ x ∈ (s₀ j).val := by
    change f₀ x ∈ ((cofiniteMixedTangentialOriginalSideEquiv θ d hθ hd hb ρ hρ hθρ hPeriod) j).val
    rw [hj]
    exact hxV
  change f₀ x ∈ f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i at hxi
  change f₀ x ∈ f₀ '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ j at hxj
  obtain ⟨u, hu, hux⟩ := hxi
  obtain ⟨v, hv, hvx⟩ := hxj
  exact _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q₀ hij
    ((f₀).injective hux ▸ hu) ((f₀).injective hvx ▸ hv)

/-- The original self-side contact point lies in the actual side interior
and is fixed by its actual original side element. -/
theorem cofiniteMixedTangential_self_foot_data (i : Fin n) (hi : ρ i = i) :
    f₀ (w₀ i) ∈ (s₀ i).val ∧
      fuchsianSideElement hD₀ (s₀ i) • f₀ (w₀ i) = f₀ (w₀ i) ∧
      IsFuchsianPolygonSideInterior (P₀).cayleyData D₀ (f₀ (w₀ i)) := by
  have hmem : f₀ (w₀ i) ∈ (s₀ i).val :=
    ⟨w₀ i, cofiniteTangential_foot_mem_side θ d hθ hd hb i, rfl⟩
  have hfix : ((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)) • w₀ i = w₀ i := by
    change (S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i) (w₀ i) = w₀ i
    rw [cofiniteTangentialJordanSidePairing_element_index, hi]
    exact cofiniteTangentPairingElement_self_foot θ d hθ hd hb i
  have hfixInv : ((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i))⁻¹ • w₀ i = w₀ i := by
    calc
      ((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i))⁻¹ • w₀ i =
          ((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i))⁻¹ •
            (((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)) • w₀ i) := congrArg _ hfix.symm
      _ = w₀ i := inv_smul_smul _ _
  have hfixActual : fuchsianSideElement hD₀ (s₀ i) • f₀ (w₀ i) = f₀ (w₀ i) := by
    rw [cofiniteMixedTangentialOriginalSide_element θ d hθ hd hb ρ hρ hθρ hPeriod,
      ← cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod]
    exact congrArg f₀ hfixInv
  refine ⟨hmem, hfixActual, (hD₀).nonvertex_is_side_interior ?_ ?_⟩
  · exact (s₀ i).property.subset_frontier (hD₀).locallyFinite.fundamental hmem
  · intro hvertex
    exact cofiniteMixedTangential_self_foot_nonvertex θ d hθ hd hb ρ hθρ i hi
      (cofiniteMixedTangential_actual_vertex_native θ d hθ hd hb ρ hρ hθρ hPeriod (w₀ i) hvertex)

/-- The actual full stabilizer order of the original self-side contact
point is exactly two, including mixed finite/ideal polygons. -/
theorem cofiniteMixedTangential_self_foot_pointOrder (i : Fin n) (hi : ρ i = i) :
    fuchsianPointOrder (P₀).cayleyData (f₀ (w₀ i)) = 2 := by
  obtain ⟨hm, hf, hI⟩ := cofiniteMixedTangential_self_foot_data θ d hθ hd hb ρ hρ hθρ hPeriod i hi
  exact (hD₀).side_interior_fixed_order_two (s₀ i) hm hI hf

/-- The actual original closed-polygon cycle of a self-side contact
point is a singleton, with all whole-group elements included. -/
theorem cofiniteMixedTangential_self_foot_cycle (i : Fin n) (hi : ρ i = i) :
    fuchsianPolygonCycle (P₀).cayleyData D₀ (f₀ (w₀ i)) = {f₀ (w₀ i)} := by
  obtain ⟨hm, hf, hI⟩ := cofiniteMixedTangential_self_foot_data θ d hθ hd hb ρ hρ hθρ hPeriod i hi
  exact (hD₀).side_interior_fixed_cycle_singleton (s₀ i) hm hI hf

/-- Distinct actual self-side labels cannot have contact points in the
same orbit of the entire original native group. -/
theorem cofiniteMixedTangential_self_foot_orbit_injective (i j : Fin n) (hi : ρ i = i) (hj : ρ j = j)
    (g : (S₀).Generated) (hg : g.val (w₀ i) = w₀ j) : i = j := by
  have hmem : f₀ (w₀ j) ∈ closure D₀ := by
    have hm := (cofiniteMixedTangential_self_foot_data θ d hθ hd hb ρ hρ hθρ hPeriod j hj).1
    exact frontier_subset_closure ((s₀ j).property.subset_frontier (hD₀).locallyFinite.fundamental hm)
  have hcycle : f₀ (w₀ j) ∈ fuchsianPolygonCycle (P₀).cayleyData D₀ (f₀ (w₀ i)) := by
    refine ⟨hmem, MulAction.mem_orbit_iff.mpr ⟨E₀ g, ?_⟩⟩
    exact (cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod g (w₀ i)).symm.trans
      (congrArg f₀ hg)
  rw [cofiniteMixedTangential_self_foot_cycle θ d hθ hd hb ρ hρ hθρ hPeriod i hi] at hcycle
  have heq : w₀ j = w₀ i := (f₀).injective (Set.mem_singleton_iff.mp hcycle)
  by_contra hij
  exact cofiniteMixedTangential_self_foot_nonvertex θ d hθ hd hb ρ hθρ i hi
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q₀ hij
      (cofiniteTangential_foot_mem_side θ d hθ hd hb i)
      (heq ▸ cofiniteTangential_foot_mem_side θ d hθ hd hb j))

/-- No actual self-side contact point shares a whole native group orbit
with any genuine original finite vertex. -/
theorem cofiniteMixedTangential_self_foot_not_vertex_orbit (i j : Fin n) (hi : ρ i = i)
    (x : ℍ) (hx : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) = (Q₀).vertices j)
    (g : (S₀).Generated) (hg : g.val (w₀ i) = x) : False := by
  have hxP : x ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier := by
    apply (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ j)
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) ∈ _root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (Q₀).vertices j
    rw [hx]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _
  have hmem : f₀ x ∈ closure D₀ := by
    rw [← cofiniteMixedTangential_original_carrier_image θ d hθ hd hb ρ hρ hθρ hPeriod]
    exact ⟨x, hxP, rfl⟩
  have hcycle : f₀ x ∈ fuchsianPolygonCycle (P₀).cayleyData D₀ (f₀ (w₀ i)) := by
    refine ⟨hmem, MulAction.mem_orbit_iff.mpr ⟨E₀ g, ?_⟩⟩
    exact (cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod g (w₀ i)).symm.trans
      (congrArg f₀ hg)
  rw [cofiniteMixedTangential_self_foot_cycle θ d hθ hd hb ρ hρ hθρ hPeriod i hi] at hcycle
  have heq : x = w₀ i := (f₀).injective (Set.mem_singleton_iff.mp hcycle)
  exact cofiniteMixedTangential_self_foot_nonvertex θ d hθ hd hb ρ hθρ i hi
    ⟨j, hx.symm.trans (congrArg (fun y : ℍ => _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y)) heq)⟩

end MixedSelfCenters
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology

section MixedFiniteClasses
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "S₀" => cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
local notation "τ₀" => ρ.trans (finRotate n)
local notation "C₀" => fun x:ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)
local notation "R₀" => Relation.EqvGen (fun i j:Fin n=>j=τ₀ i)

/-- A literal original side step carries a finite vertex to exactly its
natural successor or predecessor, retaining the original corner class. -/
theorem cofiniteMixedTangential_vertex_step_label (a b:(S₀).Copy)
    (hab:(S₀).Step a b) (i:Fin n) (hi:C₀ a.2.val=(Q₀).vertices i) :
    ∃j:Fin n,C₀ b.2.val=(Q₀).vertices j ∧R₀ i j := by
  rcases hab with rfl|⟨s,has,hpoint,_hgroup⟩
  · exact ⟨i,hi,Relation.EqvGen.refl _⟩
  have hlabels:=cofiniteJordan_vertex_side_labels Q₀ i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc a.2.val)
    hi.symm s (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using has)
  have hmap (k:Fin n) (hk:s=_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ k) :
      (cofiniteTangentPairingClosedIsometry θ d hθ hd hb k (ρ k)).closedMap (C₀ a.2.val)=C₀ b.2.val := by
    have hp:b.2.val=cofiniteTangentPairingElement θ d hθ hd hb k (ρ k) a.2.val:=by
      change b.2.val=(S₀).element s a.2.val at hpoint
      rw [hk,cofiniteTangentialJordanSidePairing_element_index] at hpoint
      exact hpoint
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes,cofiniteTangentPairingClosedIsometry_finite,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,←hp]
  rcases hlabels with hin|hout
  · let k:=(finRotate n).symm i
    have hclosed:=hmap k hin
    rw [hi,show i=finRotate n k from ((finRotate n).apply_symm_apply i).symm,
      cofiniteTangentPairingClosedIsometry_vertex_right θ d hθ hd hb k (ρ k)
        (cofiniteTangentialPairing_other_angle θ ρ hρ hθρ k)] at hclosed
    refine ⟨ρ k,hclosed.symm,Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ?_)⟩
    change i=finRotate n (ρ (ρ k))
    rw [hρ]
    exact ((finRotate n).apply_symm_apply i).symm
  · have hclosed:=hmap i hout
    rw [hi,cofiniteTangentPairingClosedIsometry_vertex_left θ d hθ hd hb i (ρ i) (hθρ i)] at hclosed
    exact ⟨τ₀ i,hclosed.symm,Relation.EqvGen.rel _ _ rfl⟩

/-- Every literal gluing chain starting at a genuine finite corner retains
its complete original natural corner class. -/
theorem cofiniteMixedTangential_vertex_chain_label (a b:(S₀).Copy)
    (hab:Relation.EqvGen (S₀).Step a b) (i:Fin n) (hi:C₀ a.2.val=(Q₀).vertices i) :
    ∃j:Fin n,C₀ b.2.val=(Q₀).vertices j ∧R₀ i j := by
  let U:(S₀).Copy→Prop:=fun c=>∃j:Fin n,C₀ c.2.val=(Q₀).vertices j ∧R₀ i j
  have hstep (u v:(S₀).Copy) (huv:(S₀).Step u v) : U u→U v:=by
    rintro ⟨j,hj,hij⟩
    obtain ⟨k,hk,hjk⟩:=cofiniteMixedTangential_vertex_step_label θ d hθ hd hb ρ hρ hθρ u v huv j hj
    exact ⟨k,hk,Relation.EqvGen.trans _ _ _ hij hjk⟩
  have hiff:U a↔U b:=by
    clear hi
    induction hab with
    | rel u v huv=>exact ⟨hstep u v huv,hstep v u ((S₀).step_symm huv)⟩
    | refl _=>rfl
    | symm _ _ _ ih=>exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂=>exact ih₁.trans ih₂
  exact hiff.mp ⟨i,hi,Relation.EqvGen.refl _⟩

variable (hPeriod:∀i:Fin n,0<θ i→∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
include hPeriod
local notation "P₀" => cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => f₀ '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q₀)

/-- Whole-group orbit coincidences of actual finite corners imply the
unchanged natural corner relation; no generating-set shortcut is used. -/
theorem cofiniteMixedTangential_vertex_orbit_label (i j:Fin n) (x y:ℍ)
    (hx:C₀ x=(Q₀).vertices i) (hy:C₀ y=(Q₀).vertices j)
    (g:(S₀).Generated) (hgy:g.val y=x) : R₀ i j := by
  have hxP:x∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier:=by
    apply (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)
    change C₀ x∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (Q₀).vertices i
    rw [hx]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _
  have hyP:y∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier:=by
    apply (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ j)
    change C₀ y∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (Q₀).vertices j
    rw [hy]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _
  let p:(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).Point:=⟨x,hxP⟩
  let q:(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).Point:=⟨y,hyP⟩
  have he:(S₀).project (1,p)=(S₀).project (g,q):=by
    apply cofiniteMixedTangential_evaluation_injective θ d hθ hd hb ρ hρ hθρ hPeriod
    exact hgy.symm
  obtain ⟨k,hk,hik⟩:=cofiniteMixedTangential_vertex_chain_label θ d hθ hd hb ρ hρ hθρ
    (1,p) (g,q) (((S₀).project_eq_iff _ _).mp he) i hx
  have hkj:k=j:=(Q₀).vertices_injective (hk.symm.trans hy)
  exact hkj ▸ hik

/-- The actual original finite-vertex angle is precisely its prescribed
geometric angle, also when other corners of the polygon are ideal. -/
theorem cofiniteMixedTangential_vertex_angle (i:Fin n) (z:𝔻)
    (hz:(Q₀).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    fuchsianPolygonAngle (P₀).cayleyData D₀ (f₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))=θ i := by
  have hCF:(P₀).cayleyData.finiteCoordinate ''closure D₀=(Q₀).finiteCarrier:=by
    rw [(P₀).cayleyData.finiteCoordinate.image_closure,
      cofiniteMixedTangential_projective_disc_finite_region θ d hθ hd hb ρ hρ hθρ hPeriod,
      (Q₀).finiteCarrier_eq_closure]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle ((P₀).cayleyData.finiteCoordinate ''closure D₀)
    ((P₀).cayleyData.finiteCoordinate (f₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)))=θ i
  rw [hCF,HalfPlaneFuchsianGroup.cayleyCoordinate_finite,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  rw [←_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle θ d hθ hd hb i]
  exact (convexPolygon_angle_eq_subtended Q₀ (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex θ d hθ hd hb) i z hz).symm

end MixedFiniteClasses
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology
open scoped Classical

section MixedActualVertexCycles
variable {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi)
    (ρ:Equiv.Perm (Fin n)) (hρ:Function.Involutive ρ)
    (hθρ:∀i,θ i=θ (finRotate n (ρ i)))
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
local notation "S₀" => cofiniteTangentialSidePairing θ d hθ hd hb ρ hρ hθρ
local notation "τ₀" => ρ.trans (finRotate n)
local notation "R₀" => Relation.EqvGen (fun i j:Fin n=>j=τ₀ i)

/-- Actual finite corners use their literal original complex coordinate;
ideal indices have an unused default point. -/
def cofiniteMixedTangentialVertexDisc (i:Fin n) : 𝔻 :=
  if h:‖((Q₀).vertices i:ℂ)‖<1 then Complex.UnitDisc.mk ((Q₀).vertices i:ℂ) h else 0

local notation "z₀" => cofiniteMixedTangentialVertexDisc θ d hθ hd hb

theorem cofiniteMixedTangentialVertexDisc_coordinate (i:Fin n) (hi:0<θ i) :
    (Q₀).vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (z₀ i) := by
  have hf:=cofiniteTangential_positive_vertex_finite θ d hθ hd hb i hi
  simp only [cofiniteMixedTangentialVertexDisc,dite_eq_left hf]
  exact Subtype.ext rfl

include hθρ

theorem cofiniteMixedTangential_corner_relation_angle {i j:Fin n} (hij:R₀ i j) :
    θ j=θ i := by
  induction hij with
  | rel i j hij=>rw [hij];exact (hθρ i).symm
  | refl _=>rfl
  | symm _ _ _ ih=>exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂=>exact ih₂.trans ih₁

/-- Each genuine natural corner chain is realized by actual whole-group
elements on the unchanged finite polygon vertices. -/
theorem cofiniteMixedTangential_corner_relation_orbit {i j:Fin n} (hij:R₀ i j)
    (hi:0<θ i) : ∃g:(S₀).Generated,g.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ i))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ j) := by
  induction hij with
  | rel i j hij=>
    refine ⟨(S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i),?_⟩
    rw [hij]
    change (S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ i))=_
    rw [cofiniteTangentialJordanSidePairing_element_index]
    exact cofiniteTangentialJordanPairing_vertex θ d hθ hd hb ρ hθρ z₀
      (cofiniteMixedTangentialVertexDisc_coordinate θ d hθ hd hb) i hi
  | refl i=>exact ⟨1,rfl⟩
  | symm i j hij ih=>
    have hj:0<θ i:=by rwa [←cofiniteMixedTangential_corner_relation_angle θ ρ hθρ hij]
    obtain ⟨g,hg⟩:=ih hj
    refine ⟨g⁻¹,?_⟩
    change g.val.symm _=_
    rw [←hg,g.val.symm_apply_apply]
  | trans i j k hij _ ih₁ ih₂=>
    obtain ⟨g,hg⟩:=ih₁ hi
    have hj:0<θ j:=by rwa [cofiniteMixedTangential_corner_relation_angle θ ρ hθρ hij]
    obtain ⟨h,hh⟩:=ih₂ hj
    refine ⟨h*g,?_⟩
    change h.val (g.val _)=_
    rw [hg,hh]

variable (hPeriod:∀i:Fin n,0<θ i→∃N:ℕ,3≤N ∧((ρ.trans (finRotate n))^[N]) i=i ∧θ i=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
include hPeriod
local notation "P₀" => cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => f₀ '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q₀)
local notation "E₀" => MulEquiv.trans (cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ)
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))
local notation "hD₀" => cofiniteMixedTangential_projective_disc_convex θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "p₀" => fun i:Fin n=>f₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ i))

/-- The entire original finite cycle consists of exactly the original
labels in the genuine natural corner class. -/
def cofiniteMixedTangentialVertexCycleEquiv (i:Fin n) (hi:0<θ i) :
    {j:Fin n//R₀ i j} ≃ fuchsianPolygonCycle (P₀).cayleyData D₀ (p₀ i) := by
  let f:{j:Fin n//R₀ i j}→fuchsianPolygonCycle (P₀).cayleyData D₀ (p₀ i):=fun j=>by
    have hj:0<θ j.val:=by rwa [cofiniteMixedTangential_corner_relation_angle θ ρ hθρ j.property]
    have hz:=cofiniteMixedTangentialVertexDisc_coordinate θ d hθ hd hb j.val hj
    have hx:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ j.val)∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier:=by
      apply (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ j.val)
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ j.val)))∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (Q₀).vertices j.val
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,←hz]
      exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _
    refine ⟨p₀ j.val,?_,?_⟩
    · rw [←cofiniteMixedTangential_original_carrier_image θ d hθ hd hb ρ hρ hθρ hPeriod]
      exact ⟨_,hx,rfl⟩
    · obtain ⟨g,hg⟩:=cofiniteMixedTangential_corner_relation_orbit θ d hθ hd hb ρ hρ hθρ j.property hi
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨E₀ g,?_⟩
      rw [←cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod,hg]
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro j k hjk
    have hp:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ j.val)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ k.val):=
      (f₀).injective (congrArg Subtype.val hjk)
    have hj:0<θ j.val:=by rwa [cofiniteMixedTangential_corner_relation_angle θ ρ hθρ j.property]
    have hk:0<θ k.val:=by rwa [cofiniteMixedTangential_corner_relation_angle θ ρ hθρ k.property]
    apply Subtype.ext
    apply (Q₀).vertices_injective
    rw [cofiniteMixedTangentialVertexDisc_coordinate θ d hθ hd hb j.val hj,
      cofiniteMixedTangentialVertexDisc_coordinate θ d hθ hd hb k.val hk]
    exact congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm.injective hp)
  · intro y
    have hy:y.val∈closure D₀:=y.property.1
    rw [←cofiniteMixedTangential_original_carrier_image θ d hθ hd hb ρ hρ hθρ hPeriod] at hy
    obtain ⟨x,hx,hxy⟩:=hy
    obtain ⟨a,ha⟩:=MulAction.mem_orbit_iff.mp y.property.2
    let g:=(E₀).symm a
    have hg:g.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ i))=x:=by
      apply (f₀).injective
      rw [cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod,
        (E₀).apply_symm_apply,ha]
      exact hxy.symm
    have hxi:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ i)∈(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier:=by
      apply (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ i)))∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonEdge (Q₀).vertices i
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,←cofiniteMixedTangentialVertexDisc_coordinate θ d hθ hd hb i hi]
      exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _
    let xp:(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).Point:=⟨x,hx⟩
    let ip:(_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).Point:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ i),hxi⟩
    have he:(S₀).project (g,ip)=(S₀).project (1,xp):=by
      apply cofiniteMixedTangential_evaluation_injective θ d hθ hd hb ρ hρ hθρ hPeriod
      exact hg
    obtain ⟨j,hj,hij⟩:=cofiniteMixedTangential_vertex_chain_label θ d hθ hd hb ρ hρ hθρ
      (g,ip) (1,xp) (((S₀).project_eq_iff _ _).mp he) i
      (by
        change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ i)))=(Q₀).vertices i
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
        exact (cofiniteMixedTangentialVertexDisc_coordinate θ d hθ hd hb i hi).symm)
    have hjpos:0<θ j:=by rwa [cofiniteMixedTangential_corner_relation_angle θ ρ hθρ hij]
    refine ⟨⟨j,hij⟩,Subtype.ext ?_⟩
    change f₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ j))=y.val
    rw [←hxy]
    apply congrArg f₀
    have hxj:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)=(Q₀).vertices j:=hj
    have hzz:z₀ j=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective
      ((cofiniteMixedTangentialVertexDisc_coordinate θ d hθ hd hb j hjpos).symm.trans hxj.symm)
    rw [hzz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]

theorem cofiniteMixedTangentialVertexCycleEquiv_apply (i:Fin n) (hi:0<θ i) (j:{j:Fin n//R₀ i j}) :
    (cofiniteMixedTangentialVertexCycleEquiv θ d hθ hd hb ρ hρ hθρ hPeriod i hi j).val=p₀ j.val := rfl

/-- The prescribed angle sum over the entire genuine natural corner class
is the original finite-cycle angle and therefore determines the actual full stabilizer. -/
theorem cofiniteMixedTangential_vertex_class_angle_sum (i:Fin n) (hi:0<θ i) :
    (∑j:{j:Fin n//R₀ i j},θ j.val)=
      2*Real.pi/fuchsianPointOrder (P₀).cayleyData (p₀ i) := by
  classical
  let e:=cofiniteMixedTangentialVertexCycleEquiv θ d hθ hd hb ρ hρ hθρ hPeriod i hi
  have hs:(∑j:{j:Fin n//R₀ i j},θ j.val)=
      ∑y∈((hD₀).locallyFinite.cycle_finite (p₀ i)).toFinset,fuchsianPolygonAngle (P₀).cayleyData D₀ y:=by
    apply Finset.sum_bij (fun j _=>(e j).val)
    · intro j _
      exact ((hD₀).locallyFinite.cycle_finite (p₀ i)).mem_toFinset.mpr (e j).property
    · intro j _ k _ he
      exact e.injective (Subtype.ext he)
    · intro y hy
      let q:fuchsianPolygonCycle (P₀).cayleyData D₀ (p₀ i):=
        ⟨y,((hD₀).locallyFinite.cycle_finite (p₀ i)).mem_toFinset.mp hy⟩
      exact ⟨e.symm q,Finset.mem_univ _,congrArg Subtype.val (e.apply_symm_apply q)⟩
    · intro j _
      rw [cofiniteMixedTangentialVertexCycleEquiv_apply]
      have hj:0<θ j.val:=by rwa [cofiniteMixedTangential_corner_relation_angle θ ρ hθρ j.property]
      exact (cofiniteMixedTangential_vertex_angle θ d hθ hd hb ρ hρ hθρ hPeriod j.val (z₀ j.val)
        (cofiniteMixedTangentialVertexDisc_coordinate θ d hθ hd hb j.val hj)).symm
  exact hs.trans (sum_cycle_angles_eq_two_pi_div_pointOrder hD₀ (p₀ i))

end MixedActualVertexCycles
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology
open scoped Classical

/-- Every genuine outer mark has a singleton original natural corner class. -/
theorem cofiniteConstruction_outer_class_singleton (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hB:2≤4*g+ms.length) (j:{j:Fin ms.length//ms[j]≠2})
    (i:Fin (cofiniteConstructionAngles g ms last).length) :
    (cofiniteConstructionCornerSetoid g ms last).r (cofiniteConstructionOuterIndex g ms last j) i ↔
      i=cofiniteConstructionOuterIndex g ms last j := by
  rw [←cofiniteConstructionCornerClassMap_eq_iff g ms last hB]
  let e:=cofiniteConstructionCornerLabelEquiv g ms last hB
  have ho:e (Sum.inr j)=cofiniteConstructionOuterIndex g ms last j:=
    cofiniteConstructionCornerLabelEquiv_outer g ms last hB j
  obtain ⟨a,rfl⟩:=e.surjective i
  rw [←ho]
  change Sum.elim (fun _=>none) some (e.symm (e (Sum.inr j)))=
    Sum.elim (fun _=>none) some (e.symm (e a)) ↔e a=e (Sum.inr j)
  rw [e.symm_apply_apply,e.symm_apply_apply,e.injective.eq_iff]
  cases a <;> simp [eq_comm]

/-- The exact prescribed outer angle is the entire genuine corner-class sum. -/
theorem cofiniteConstruction_outer_class_angle_sum (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hB:2≤4*g+ms.length) (j:{j:Fin ms.length//ms[j]≠2}) :
    (∑i:{i:Fin (cofiniteConstructionAngles g ms last).length//
      (cofiniteConstructionCornerSetoid g ms last).r (cofiniteConstructionOuterIndex g ms last j) i},
      (cofiniteConstructionAngles g ms last)[i.val])=
        cofiniteConstructionConeAngle ms[j.val] := by
  let a:{i:Fin (cofiniteConstructionAngles g ms last).length//
      (cofiniteConstructionCornerSetoid g ms last).r (cofiniteConstructionOuterIndex g ms last j) i}:=
    ⟨cofiniteConstructionOuterIndex g ms last j,Relation.EqvGen.refl _⟩
  have hs:(∑i:{i:Fin (cofiniteConstructionAngles g ms last).length//
      (cofiniteConstructionCornerSetoid g ms last).r (cofiniteConstructionOuterIndex g ms last j) i},
      (cofiniteConstructionAngles g ms last)[i.val])=
        (cofiniteConstructionAngles g ms last)[a.val]:=by
    apply Finset.sum_eq_single a
    · intro b _ hb
      exact False.elim (hb (Subtype.ext
        ((cofiniteConstruction_outer_class_singleton g ms last hB j b.val).mp b.property)))
    · simp
  rw [hs]
  exact cofiniteConstructionOuterIndex_angle g ms last j

/-- The original whole-group stabilizer at each finite outer mark has its prescribed exact order, proved by the actual cycle-angle formula. -/
theorem cofiniteConstruction_mixed_outer_pointOrder (g:ℕ) (ms:List ℕ) (last:ℕ)
    (hms:∀m∈ms,m=0∨2≤m) (hlast:last=0∨2≤last)
    (hdef:0<cofiniteConstructionDeficit g ms last) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i=>(cofiniteConstructionAngles g ms last)[i]) d=Real.pi)
    (j:{j:Fin ms.length//2<ms[j]}) :
    let θ:Fin (cofiniteConstructionAngles g ms last).length→ℝ:=fun i=>(cofiniteConstructionAngles g ms last)[i]
    let hθ:∀i,θ i∈Ico (0:ℝ) Real.pi:=fun i=>cofiniteConstruction_angles_mem g ms last hms hlast hdef _
      (List.getElem_mem i.isLt)
    let ρ:=cofiniteConstructionPairing g ms last
    let hρ:=cofiniteConstructionPairing_involutive g ms last
    let hθρ:=cofiniteConstructionPairing_angle_profile g ms last
    let hPeriod:=cofiniteConstruction_mixed_angular_periods g ms last hms hlast hdef
    let P:=cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
    let i:=cofiniteConstructionOuterIndex g ms last ⟨j.val,by omega⟩
    fuchsianPointOrder P.cayleyData (P.cayleyCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (cofiniteMixedTangentialVertexDisc θ d hθ hd hb i)))=ms[j.val] := by
  intro θ hθ ρ hρ hθρ hPeriod P i
  have hm:0<ms[j.val]:=by omega
  have hmr:(0:ℝ)<ms[j.val]:=by exact_mod_cast hm
  have hi:0<θ i:=by
    rw [show θ i=cofiniteConstructionConeAngle ms[j.val] from
      cofiniteConstructionOuterIndex_angle g ms last ⟨j.val,by omega⟩]
    exact div_pos (by positivity) hmr
  have hsum:=cofiniteMixedTangential_vertex_class_angle_sum θ d hθ hd hb ρ hρ hθρ hPeriod i hi
  change (∑k:{k:Fin (cofiniteConstructionAngles g ms last).length//
      (cofiniteConstructionCornerSetoid g ms last).r i k},θ k.val)=_ at hsum
  rw [cofiniteConstruction_outer_class_angle_sum g ms last
    (cofiniteConstruction_base_count g ms last hdef) ⟨j.val,by omega⟩] at hsum
  have hpo:=P.cayleyData.pointOrder_pos (P.cayleyCoordinate
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (cofiniteMixedTangentialVertexDisc θ d hθ hd hb i)))
  have hpor:(0:ℝ)<fuchsianPointOrder P.cayleyData (P.cayleyCoordinate
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (cofiniteMixedTangentialVertexDisc θ d hθ hd hb i))):=by exact_mod_cast hpo
  have hreal:((fuchsianPointOrder P.cayleyData (P.cayleyCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (cofiniteMixedTangentialVertexDisc θ d hθ hd hb i)))):ℝ)=(ms[j.val]:ℝ):=by
    have he:2*Real.pi*(fuchsianPointOrder P.cayleyData (P.cayleyCoordinate
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (cofiniteMixedTangentialVertexDisc θ d hθ hd hb i))):ℝ)=2*Real.pi*(ms[j.val]:ℝ):=
      (div_eq_div_iff hmr.ne' hpor.ne').mp hsum
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero) he
  exact_mod_cast hreal

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology
open scoped Classical

section CuspedEllipticClasses
variable (g:ℕ) (ms:List ℕ) (hms:∀m∈ms,m=0∨2≤m)
    (hdef:0<cofiniteConstructionDeficit g ms 0) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms 0).length=>
      (cofiniteConstructionAngles g ms 0)[i]) d=Real.pi)
local notation "θ₀" => fun i:Fin (cofiniteConstructionAngles g ms 0).length=>(cofiniteConstructionAngles g ms 0)[i]
local notation "hθ₀" => fun i:Fin (cofiniteConstructionAngles g ms 0).length=>
  cofiniteConstruction_angles_mem g ms 0 hms (Or.inl rfl) hdef _ (List.getElem_mem (Fin.isLt i))
local notation "ρ₀" => cofiniteConstructionPairing g ms 0
local notation "hρ₀" => cofiniteConstructionPairing_involutive g ms 0
local notation "hθρ₀" => cofiniteConstructionPairing_angle_profile g ms 0
local notation "hPeriod₀" => cofiniteConstruction_mixed_angular_periods g ms 0 hms (Or.inl rfl) hdef

/-- The original whole projective group, retaining the prescribed mixed
side generators and their concrete occurrence labels. -/
def cofiniteConstructionCuspedMobiusGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  cofiniteMixedTangentialMobiusGroup θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀

/-- Genuine half-plane Fuchsian data of this same concrete whole group. -/
theorem cofiniteConstructionCuspedHalfPlaneData :
    HalfPlaneFuchsianGroup (cofiniteConstructionCuspedMobiusGroup g ms hms hdef d hd hb) :=
  cofiniteMixedTangentialHalfPlaneData θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀

local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ₀ d hθ₀ hd hb
local notation "S₀" => cofiniteTangentialSidePairing θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀
local notation "H₀" => _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
  (cofiniteConstructionCuspedMobiusGroup g ms hms hdef d hd hb)
local notation "P₀" => cofiniteConstructionCuspedHalfPlaneData g ms hms hdef d hd hb
local notation "f₀" => HalfPlaneFuchsianGroup.cayleyCoordinate P₀
local notation "D₀" => f₀ '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q₀)

/-- Faithful identification of the original native action with its
actual projective action in the same Cayley disc. -/
def cofiniteConstructionCuspedCayleyEquiv : (S₀).Generated ≃* H₀ :=
  (cofiniteMixedTangentialGroupEquiv θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀).trans
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
      (cofiniteMixedTangentialMobiusGroup θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀))

local notation "E₀" => cofiniteConstructionCuspedCayleyEquiv g ms hms hdef d hd hb
local notation "hD₀" => cofiniteMixedTangential_projective_disc_convex θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀
local notation "w₀" => fun i:Fin (cofiniteConstructionAngles g ms 0).length=>
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ₀ d hd (finRotate _ i))
local notation "z₀" => cofiniteMixedTangentialVertexDisc θ₀ d hθ₀ hd hb

/-- The finite occurrence uses its original corner, or its genuine
self-side contact point when its prescribed order is two. -/
def cofiniteConstructionCuspedConePoint (j:{j:Fin ms.length//ms[j]≠0}) : ℍ :=
  if hj:ms[j.val]=2 then w₀ (cofiniteConstructionSelfSideIndex g ms 0 ⟨j.val,hj⟩)
  else _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (z₀ (cofiniteConstructionOuterIndex g ms 0 ⟨j.val,hj⟩))

local notation "p₀" => cofiniteConstructionCuspedConePoint g ms hms hdef d hd hb

/-- Every retained occurrence has precisely its prescribed whole-group
stabilizer order; cusps are not counted as finite occurrences. -/
theorem cofiniteConstruction_cusped_cone_pointOrder (j:{j:Fin ms.length//ms[j]≠0}) :
    fuchsianPointOrder (P₀).cayleyData (f₀ (p₀ j))=ms[j.val] := by
  by_cases hj:ms[j.val]=2
  · rw [cofiniteConstructionCuspedConePoint,dite_eq_left hj]
    exact (cofiniteMixedTangential_self_foot_pointOrder θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀
      _ (cofiniteConstructionSelfSideIndex_fixed g ms 0 ⟨j.val,hj⟩)).trans hj.symm
  · rw [cofiniteConstructionCuspedConePoint,dite_eq_right hj]
    have hm:2<ms[j.val]:=by
      change 2<ms[j.val.val]
      have hz:ms[j.val.val]≠0:=j.property
      have ht:ms[j.val.val]≠2:=hj
      rcases hms _ (List.getElem_mem j.val.isLt) with h|h <;> omega
    exact cofiniteConstruction_mixed_outer_pointOrder g ms 0 hms (Or.inl rfl) hdef d hd hb ⟨j.val,hm⟩

/-- Each finite occurrence is a genuine fixed point of an actual elliptic
element of the entire constructed group. -/
theorem cofiniteConstruction_cusped_cone_elliptic (j:{j:Fin ms.length//ms[j]≠0}) :
    (f₀ (p₀ j)).val∈fuchsianCyclicFixedPoints (P₀).cayleyData.asFuchsianDisc .elliptic := by
  have hm:2≤ms[j.val]:=by
    change 2≤ms[j.val.val]
    have hz:ms[j.val.val]≠0:=j.property
    rcases hms _ (List.getElem_mem j.val.isLt) with h|h <;> omega
  have hn:¬IsAccidentalFuchsianPoint (P₀).cayleyData (f₀ (p₀ j)):=by
    intro ha
    have he:=(isAccidentalFuchsianPoint_iff_pointOrder_one (P₀).cayleyData _).mp ha
    rw [cofiniteConstruction_cusped_cone_pointOrder] at he
    omega
  obtain ⟨a,ha,hfix⟩:=not_not.mp hn
  exact ⟨fun _=>(f₀ (p₀ j)).property,a.val,a.property,ha,congrArg Subtype.val hfix⟩

def cofiniteConstructionCuspedEllipticPoint (j:{j:Fin ms.length//ms[j]≠0}) :
    fuchsianCyclicFixedPoints (P₀).cayleyData.asFuchsianDisc .elliptic :=
  ⟨(f₀ (p₀ j)).val,cofiniteConstruction_cusped_cone_elliptic g ms hms hdef d hd hb j⟩

/-- A finite outer occurrence is an unchanged finite original vertex. -/
theorem cofiniteConstruction_cusped_outer_coordinate (j:{j:Fin ms.length//ms[j]≠0}) (hj:ms[j.val]≠2) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (p₀ j))=
      (Q₀).vertices (cofiniteConstructionOuterIndex g ms 0 ⟨j.val,hj⟩) := by
  have hm:0<ms[j.val]:=Nat.pos_of_ne_zero j.property
  have hr:(0:ℝ)<ms[j.val]:=by exact_mod_cast hm
  have hi:0<θ₀ (cofiniteConstructionOuterIndex g ms 0 ⟨j.val,hj⟩):=by
    change 0<(cofiniteConstructionAngles g ms 0)[cofiniteConstructionOuterIndex g ms 0 ⟨j.val,hj⟩]
    rw [cofiniteConstructionOuterIndex_angle]
    exact div_pos (by positivity) hr
  rw [cofiniteConstructionCuspedConePoint,dite_eq_right hj,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  exact (cofiniteMixedTangentialVertexDisc_coordinate θ₀ d hθ₀ hd hb _ hi).symm

/-- Distinct finite occurrences remain distinct even modulo the whole
original native group, including the order-two side centres. -/
theorem cofiniteConstruction_cusped_cone_orbits_distinct (i j:{j:Fin ms.length//ms[j]≠0})
    (a:(S₀).Generated) (ha:a.val (p₀ i)=p₀ j) : i=j := by
  by_cases hi:ms[i.val]=2
  · by_cases hj:ms[j.val]=2
    · have hs:=cofiniteMixedTangential_self_foot_orbit_injective θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀
        (cofiniteConstructionSelfSideIndex g ms 0 ⟨i.val,hi⟩)
        (cofiniteConstructionSelfSideIndex g ms 0 ⟨j.val,hj⟩)
        (cofiniteConstructionSelfSideIndex_fixed g ms 0 ⟨i.val,hi⟩)
        (cofiniteConstructionSelfSideIndex_fixed g ms 0 ⟨j.val,hj⟩) a
        (by simpa only [cofiniteConstructionCuspedConePoint,dite_eq_left hi,dite_eq_left hj] using ha)
      have he:=cofiniteConstructionSelfSideIndex_injective g ms 0 hs
      have hv:i.val=j.val:=congrArg (fun k:{j:Fin ms.length//ms[j]=2}=>k.val) he
      exact Subtype.ext hv
    · exact False.elim (cofiniteMixedTangential_self_foot_not_vertex_orbit θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀
        (cofiniteConstructionSelfSideIndex g ms 0 ⟨i.val,hi⟩)
        (cofiniteConstructionOuterIndex g ms 0 ⟨j.val,hj⟩)
        (cofiniteConstructionSelfSideIndex_fixed g ms 0 ⟨i.val,hi⟩) (p₀ j)
        (cofiniteConstruction_cusped_outer_coordinate g ms hms hdef d hd hb j hj) a
        (by simpa only [cofiniteConstructionCuspedConePoint,dite_eq_left hi] using ha))
  · by_cases hj:ms[j.val]=2
    · have he:(a⁻¹).val (p₀ j)=p₀ i:=by
        change a.val.symm (p₀ j)=p₀ i
        rw [←ha,a.val.symm_apply_apply]
      exact False.elim (cofiniteMixedTangential_self_foot_not_vertex_orbit θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀
        (cofiniteConstructionSelfSideIndex g ms 0 ⟨j.val,hj⟩)
        (cofiniteConstructionOuterIndex g ms 0 ⟨i.val,hi⟩)
        (cofiniteConstructionSelfSideIndex_fixed g ms 0 ⟨j.val,hj⟩) (p₀ i)
        (cofiniteConstruction_cusped_outer_coordinate g ms hms hdef d hd hb i hi) a⁻¹
        (by simpa only [cofiniteConstructionCuspedConePoint,dite_eq_left hj] using he))
    · have hR:=cofiniteMixedTangential_vertex_orbit_label θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀
        (cofiniteConstructionOuterIndex g ms 0 ⟨i.val,hi⟩)
        (cofiniteConstructionOuterIndex g ms 0 ⟨j.val,hj⟩) (p₀ i) (p₀ j)
        (cofiniteConstruction_cusped_outer_coordinate g ms hms hdef d hd hb i hi)
        (cofiniteConstruction_cusped_outer_coordinate g ms hms hdef d hd hb j hj) a⁻¹
        (by change a.val.symm (p₀ j)=p₀ i;rw [←ha,a.val.symm_apply_apply])
      have hs:cofiniteConstructionOuterIndex g ms 0 ⟨j.val,hj⟩=
          cofiniteConstructionOuterIndex g ms 0 ⟨i.val,hi⟩:=
        (cofiniteConstruction_outer_class_singleton g ms 0
          (cofiniteConstruction_base_count g ms 0 hdef) ⟨i.val,hi⟩ _).mp hR
      have he:= (cofiniteConstructionCornerLabelEquiv g ms 0
        (cofiniteConstruction_base_count g ms 0 hdef)).injective
        (show (cofiniteConstructionCornerLabelEquiv g ms 0
          (cofiniteConstruction_base_count g ms 0 hdef)) (Sum.inr ⟨j.val,hj⟩)=
          (cofiniteConstructionCornerLabelEquiv g ms 0
          (cofiniteConstruction_base_count g ms 0 hdef)) (Sum.inr ⟨i.val,hi⟩) by
            simpa only [cofiniteConstructionCornerLabelEquiv_outer] using hs)
      exact Subtype.ext (congrArg Subtype.val (Sum.inr.inj he)).symm

/-- Every actual elliptic point in the original closed polygon is one
of the listed finite occurrences, without an unstated stabilizer hypothesis. -/
theorem cofiniteConstruction_cusped_closure_elliptic_mark
    (y:ℍ) (hx:f₀ y∈closure D₀)
    (he:¬IsAccidentalFuchsianPoint (P₀).cayleyData (f₀ y)) :
    ∃j:{j:Fin ms.length//ms[j]≠0},f₀ y=f₀ (p₀ j) := by
  by_cases hv:IsFuchsianPolygonVertex (P₀).cayleyData D₀ (f₀ y)
  · have hyn:y∈_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀:=
      cofiniteMixedTangential_actual_vertex_native θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀ y hv
    obtain ⟨i,hi⟩:=hyn
    have hip:0<θ₀ i:=cofiniteTangential_native_vertex_positive θ₀ d hθ₀ hd hb i y hi
    obtain ⟨j,hj⟩:=cofiniteConstruction_cusped_finite_corner_labels g ms hms hdef i hip
    let k:{j:Fin ms.length//ms[j]≠0}:=⟨j.val,by have hh:=j.property;omega⟩
    have hk:ms[k.val]≠2:=by
      have hh:2<ms[j.val.val]:=j.property
      change ms[j.val.val]≠2
      omega
    refine ⟨k,congrArg f₀ ?_⟩
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc y)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (p₀ k))
    rw [cofiniteConstruction_cusped_outer_coordinate g ms hms hdef d hd hb k hk]
    exact hi.symm.trans (congrArg (Q₀).vertices hj)
  · obtain ⟨s,hxs,hs,_hI,hfix,_horder,_hcycle⟩:=
      (hD₀).nonvertex_elliptic_self_paired hx hv he
    obtain ⟨i,hi⟩:=(cofiniteMixedTangentialOriginalSideEquiv θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀).surjective s
    have hρi:ρ₀ i=i:=by
      apply (cofiniteMixedTangentialOriginalSideEquiv θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀).injective
      change cofiniteMixedTangentialOriginalSide θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀ (ρ₀ i)=_
      rw [←cofiniteMixedTangentialOriginalSide_paired θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀]
      change fuchsianPairedSide hD₀
        ((cofiniteMixedTangentialOriginalSideEquiv θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀) i)=_
      rw [hi,hs]
    obtain ⟨j,hj⟩:=(cofiniteConstructionPairing_fixed_iff g ms 0 i).mp hρi
    let k:{j:Fin ms.length//ms[j]≠0}:=⟨j.val,by have hh:ms[j.val.val]=2:=j.property;change ms[j.val.val]≠0;omega⟩
    have hkj:ms[k.val]=2:=j.property
    have hfixInv:((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i))⁻¹ • y=y:=by
      apply (f₀).injective
      change f₀ ((((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i))⁻¹).val y)=f₀ y
      rw [cofiniteMixedTangential_coordinate_action θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀,
        ←cofiniteMixedTangentialOriginalSide_element θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀]
      change fuchsianSideElement hD₀
        ((cofiniteMixedTangentialOriginalSideEquiv θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀) i) • f₀ y=f₀ y
      rw [hi]
      exact hfix
    have hfixY:cofiniteTangentPairingElement θ₀ d hθ₀ hd hb i i y=y:=by
      have hm:((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)) • y=y:=by
        calc
          ((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)) • y=
              ((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)) •
                (((S₀).generator (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i))⁻¹ • y) := congrArg _ hfixInv.symm
          _=y:=smul_inv_smul _ _
      change (S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i) y=y at hm
      rw [cofiniteTangentialJordanSidePairing_element_index,hρi] at hm
      exact hm
    have hyw:y=w₀ i:=cofiniteTangentPairingElement_fixed_subsingleton θ₀ d hθ₀ hd hb i i
      hfixY (cofiniteTangentPairingElement_self_foot θ₀ d hθ₀ hd hb i)
    refine ⟨k,congrArg f₀ ?_⟩
    rw [cofiniteConstructionCuspedConePoint,dite_eq_left hkj]
    exact hyw.trans (congrArg w₀ hj.symm)

/-- Every genuine elliptic fixed-point orbit is represented by one of
the original nonzero-order occurrences. -/
theorem cofiniteConstruction_cusped_elliptic_orbit
    (p:fuchsianCyclicFixedPoints (P₀).cayleyData.asFuchsianDisc .elliptic) :
    ∃j:{j:Fin ms.length//ms[j]≠0},∃a:H₀,
      a • p=cofiniteConstructionCuspedEllipticPoint g ms hms hdef d hd hb j := by
  let x:(P₀).cayleyData.domain.carrier:=⟨p.val,p.property.1 rfl⟩
  have hx:¬IsAccidentalFuchsianPoint (P₀).cayleyData x:=by
    intro ha
    obtain ⟨a,haH,haE,haf⟩:=p.property.2
    exact ha ⟨⟨a,haH⟩,haE,Subtype.ext haf⟩
  obtain ⟨y,hy⟩:=(hD₀).locallyFinite.fundamental.cycle_nonempty x
  have hyE:¬IsAccidentalFuchsianPoint (P₀).cayleyData y:=by
    intro he
    apply hx
    apply (isAccidentalFuchsianPoint_iff_pointOrder_one (P₀).cayleyData x).mpr
    rw [←fuchsianPointOrder_eq_of_mem_cycle (P₀).cayleyData D₀ x y hy]
    exact (isAccidentalFuchsianPoint_iff_pointOrder_one (P₀).cayleyData y).mp he
  have hny:f₀ ((f₀).symm y)=y:=(f₀).apply_symm_apply y
  obtain ⟨j,hj⟩:=cofiniteConstruction_cusped_closure_elliptic_mark g ms hms hdef d hd hb
    ((f₀).symm y) (hny.symm ▸ hy.1) (hny.symm ▸ hyE)
  rw [hny] at hj
  obtain ⟨a,ha⟩:=MulAction.mem_orbit_iff.mp hy.2
  refine ⟨j,a,Subtype.ext ?_⟩
  change a.val.val p.val=(f₀ (p₀ j)).val
  exact congrArg (fun z:_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=>z.val) (ha.trans hj)

/-- Whole original projective orbits do not identify distinct finite
occurrences; the faithful native action proves this before passing to classes. -/
theorem cofiniteConstruction_cusped_elliptic_orbits_distinct (i j:{j:Fin ms.length//ms[j]≠0})
    (a:H₀)
    (ha:a • cofiniteConstructionCuspedEllipticPoint g ms hms hdef d hd hb i=
      cofiniteConstructionCuspedEllipticPoint g ms hms hdef d hd hb j) : i=j := by
  apply cofiniteConstruction_cusped_cone_orbits_distinct g ms hms hdef d hd hb i j ((E₀).symm a)
  apply (f₀).injective
  rw [cofiniteMixedTangential_coordinate_action θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀]
  change E₀ ((E₀).symm a) • f₀ (p₀ i)=f₀ (p₀ j)
  rw [(E₀).apply_symm_apply]
  have hv:=congrArg (fun p:fuchsianCyclicFixedPoints (P₀).cayleyData.asFuchsianDisc .elliptic=>p.val) ha
  exact Subtype.ext hv

/-- The original orbit class of a retained finite-order occurrence. -/
def cofiniteConstructionCuspedEllipticPointClass (j:{j:Fin ms.length//ms[j]≠0}) :
    MulAction.orbitRel.Quotient
      H₀
      (fuchsianCyclicFixedPoints (P₀).cayleyData.asFuchsianDisc .elliptic) :=
  Quotient.mk'' (cofiniteConstructionCuspedEllipticPoint g ms hms hdef d hd hb j)

theorem cofiniteConstructionCuspedEllipticPointClass_bijective :
    Function.Bijective (cofiniteConstructionCuspedEllipticPointClass g ms hms hdef d hd hb) := by
  constructor
  · intro i j he
    obtain ⟨a,ha⟩:=MulAction.mem_orbit_iff.mp (Quotient.exact he)
    exact (cofiniteConstruction_cusped_elliptic_orbits_distinct g ms hms hdef d hd hb j i a ha).symm
  · intro q
    induction q using Quotient.inductionOn' with
    | h p=>
      obtain ⟨j,a,ha⟩:=cofiniteConstruction_cusped_elliptic_orbit g ms hms hdef d hd hb p
      exact ⟨j,Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨a,ha⟩)⟩

/-- The entire actual elliptic class set is exactly the list of original
nonzero-order occurrences, including repeated equal orders separately. -/
def cofiniteConstructionCuspedEllipticClassEquiv :
    {j:Fin ms.length//ms[j]≠0} ≃ FuchsianCyclicConjugacyClasses (P₀).cayleyData.asFuchsianDisc .elliptic :=
  (Equiv.ofBijective (cofiniteConstructionCuspedEllipticPointClass g ms hms hdef d hd hb)
    (cofiniteConstructionCuspedEllipticPointClass_bijective g ms hms hdef d hd hb)).trans
      (fuchsianCyclicConjugacyClassesEquiv (P₀).cayleyData.asFuchsianDisc .elliptic).symm

/-- The genuine maximal elliptic subgroup class has exactly its original
prescribed order, rather than a divisor or a pointwise lower bound. -/
theorem cofiniteConstructionCuspedEllipticClassEquiv_order (j:{j:Fin ms.length//ms[j]≠0}) :
    fuchsianEllipticClassOrder (P₀).cayleyData.asFuchsianDisc
      (cofiniteConstructionCuspedEllipticClassEquiv g ms hms hdef d hd hb j)=ms[j.val] := by
  change fuchsianEllipticClassOrder (P₀).cayleyData.asFuchsianDisc
    (Quotient.mk _ (fuchsianCyclicPointStabilizer (P₀).cayleyData.asFuchsianDisc .elliptic
      (cofiniteConstructionCuspedEllipticPoint g ms hms hdef d hd hb j)))=_
  rw [fuchsianEllipticClassOrder_mk]
  change Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer _ (f₀ (p₀ j)).val)=_
  rw [←Nat.card_congr ((P₀).cayleyData.stabilizerEquivBoundary (f₀ (p₀ j))).toEquiv]
  exact cofiniteConstruction_cusped_cone_pointOrder g ms hms hdef d hd hb j

end CuspedEllipticClasses
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- Filtering out zero-order marks preserves exactly the individual nonzero list occurrences of each order. -/
theorem cofinite_positive_order_occurrence_count (ms : List ℕ) (m : ℕ) :
    (ms.filter (fun k => k ≠ 0)).count m =
      Nat.card {j : {j : Fin ms.length // ms[j] ≠ 0} // ms[j.val] = m} := by
  classical
  by_cases hm : m = 0
  · subst m
    let cofiniteZeroOccurrenceEmpty :
        IsEmpty {j : {j : Fin ms.length // ms[j] ≠ 0} // ms[j.val] = 0} :=
      ⟨fun j => j.val.property j.property⟩
    rw [Nat.card_of_isEmpty]
    exact List.count_eq_zero.mpr (by simp)
  · rw [List.count_filter (by simpa using hm)]
    let E : {j : {j : Fin ms.length // ms[j] ≠ 0} // ms[j.val] = m} ≃
        {j : Fin ms.length // ms[j] = m} :=
      { toFun := fun j => ⟨j.val.val, j.property⟩
        invFun := fun j => ⟨⟨j.val, by rw [j.property]; exact hm⟩, j.property⟩
        left_inv := fun j => Subtype.ext (Subtype.ext rfl)
        right_inv := fun j => rfl }
    rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact (Fin.card_filter_univ_eq_vector_get_eq_count m ⟨ms, rfl⟩).symm

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  Set
  Topology
open scoped Classical

section CuspedSignature
variable (g:ℕ) (ms:List ℕ) (hms:∀m∈ms,m=0∨2≤m)
    (hdef:0<cofiniteConstructionDeficit g ms 0) (d:ℝ) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun i:Fin (cofiniteConstructionAngles g ms 0).length=>
      (cofiniteConstructionAngles g ms 0)[i]) d=Real.pi)
local notation "θ₀" => fun i:Fin (cofiniteConstructionAngles g ms 0).length=>(cofiniteConstructionAngles g ms 0)[i]
local notation "hθ₀" => fun i:Fin (cofiniteConstructionAngles g ms 0).length=>
  cofiniteConstruction_angles_mem g ms 0 hms (Or.inl rfl) hdef _ (List.getElem_mem (Fin.isLt i))
local notation "ρ₀" => cofiniteConstructionPairing g ms 0
local notation "hρ₀" => cofiniteConstructionPairing_involutive g ms 0
local notation "hθρ₀" => cofiniteConstructionPairing_angle_profile g ms 0
local notation "hPeriod₀" => cofiniteConstruction_mixed_angular_periods g ms 0 hms (Or.inl rfl) hdef
local notation "P₀" => cofiniteConstructionCuspedHalfPlaneData g ms hms hdef d hd hb

/-- The actual elliptic order multiset is the original nonzero-order list,
with every repeated occurrence preserved by the genuine class equivalence. -/
theorem cofiniteConstruction_cusped_elliptic_orders_perm
    [Finite (FuchsianCyclicConjugacyClasses (P₀).cayleyData.asFuchsianDisc .elliptic)] :
    (ms.filter (fun m=>m≠0)).Perm (fuchsianEllipticOrderList (P₀).cayleyData.asFuchsianDisc) := by
  classical
  apply List.perm_iff_count.mpr
  intro m
  rw [cofinite_positive_order_occurrence_count,
    fuchsianEllipticOrderList_count_eq_fiber_card]
  apply Nat.card_congr
  exact (cofiniteConstructionCuspedEllipticClassEquiv g ms hms hdef d hd hb).subtypeEquiv
    (fun j=>by
      change ms[j.val]=m ↔fuchsianEllipticClassOrder (P₀).cayleyData.asFuchsianDisc
        (cofiniteConstructionCuspedEllipticClassEquiv g ms hms hdef d hd hb j)=m
      rw [cofiniteConstructionCuspedEllipticClassEquiv_order])

/-- Every mixed construction with a distinguished cusp has exactly its
prescribed actual cofinite signature. No elliptic-class, cusp, genus or
quotient-area conclusion remains among the inputs. -/
theorem cofiniteConstruction_cusped_actual_signature :
    HasCofiniteFuchsianSignature (P₀).cayleyData.asFuchsianDisc
      g (ms.filter (fun m=>m≠0)) (1+ms.count 0) := by
  apply cofiniteConstruction_cusped_signature_of_actual_orders g ms hms hdef d hd hb
  intro hFinite
  let :=hFinite
  exact cofiniteConstruction_cusped_elliptic_orders_perm g ms hms hdef d hd hb

end CuspedSignature
end LowDimensionalTopology.Geometry.Fuchsian


namespace LowDimensionalTopology.Geometry.Fuchsian

/-- Appending genuine cusp marks leaves every finite order unchanged and introduces only zero marks. -/
theorem cofinite_cusped_order_list_allowed (orders : List ℕ) (p : ℕ)
    (horders : ∀ m ∈ orders, 2 ≤ m) (m : ℕ)
    (hm : m ∈ orders ++ List.replicate (p - 1) 0) : m = 0 ∨ 2 ≤ m := by
  rcases List.mem_append.mp hm with hm | hm
  · exact Or.inr (horders m hm)
  · exact Or.inl (List.eq_of_mem_replicate hm)

/-- Removing cusp marks recovers the entire original finite-order list, including every repeated occurrence. -/
theorem cofinite_cusped_order_list_filter (orders : List ℕ) (p : ℕ)
    (horders : ∀ m ∈ orders, 2 ≤ m) :
    ((orders ++ List.replicate (p - 1) 0).filter (fun m => m ≠ 0)) = orders := by
  have hfilter : orders.filter (fun m => m ≠ 0) = orders := by
    apply List.filter_eq_self.mpr
    intro m hm
    have hpos : 0 < m := Nat.lt_of_lt_of_le (by decide : 0 < 2) (horders m hm)
    simpa only [decide_eq_true_eq] using Nat.ne_of_gt hpos
  rw [List.filter_append, hfilter]
  simp

/-- One distinguished base cusp and the appended zero marks give exactly the prescribed positive cusp count. -/
theorem cofinite_cusped_order_list_cusp_count (orders : List ℕ) (p : ℕ)
    (horders : ∀ m ∈ orders, 2 ≤ m) (hp : 1 ≤ p) :
    1 + (orders ++ List.replicate (p - 1) 0).count 0 = p := by
  have hzero : 0 ∉ orders := by
    intro hm
    exact (by decide : ¬ 2 ≤ 0) (horders 0 hm)
  rw [List.count_append, List.count_eq_zero.mpr hzero, List.count_replicate_self, Nat.zero_add]
  exact (Nat.add_comm 1 (p - 1)).trans (Nat.sub_add_cancel hp)

/-- The literal construction list has one position for each original finite-order occurrence and each additional cusp. -/
theorem cofinite_cusped_order_list_length (orders : List ℕ) (p : ℕ) :
    (orders ++ List.replicate (p - 1) 0).length = orders.length + (p - 1) := by
  simp

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set

/-- Designating one genuine cusp as the base mark leaves the full
prescribed genus, finite-order list, and cusp number in the physical deficit. -/
theorem cofiniteConstruction_cusped_orders_deficit (g : ℕ) (orders : List ℕ) (p : ℕ)
    (horders : ∀ m ∈ orders, 2 ≤ m) (hp : 1 ≤ p) :
    cofiniteConstructionDeficit g (orders ++ List.replicate (p - 1) 0) 0 =
      2 * (g : ℝ) - 2 + (p : ℝ) + (orders.map (fun m : ℕ => (1 : ℝ) - 1 / (m : ℝ))).sum := by
  rw [cofiniteConstruction_cusp_signature_deficit,
    cofinite_cusped_order_list_filter orders p horders,
    cofinite_cusped_order_list_cusp_count orders p horders hp]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set

/-- Every admissible signature with at least one cusp has an actual
first-kind finitely generated group and original convex fundamental polygon
attaining the precise lower bound with the genuine self-side subdivision. -/
theorem cofiniteConstruction_cusped_lower_side_bound_attained
    (g : ℕ) (orders : List ℕ) (p : ℕ) (horders : ∀ m ∈ orders, 2 ≤ m) (hp : 1 ≤ p)
    (hdef : 0 < 2 * (g : ℝ) - 2 + (p : ℝ) +
      (orders.map (fun m : ℕ => (1 : ℝ) - 1 / (m : ℝ))).sum) :
    ∃ H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∃ P : UnitDiscFuchsianGroup H,
      H.FG ∧ P.asFuchsianDisc.IsFirstKind ∧
      HasCofiniteFuchsianSignature P.asFuchsianDisc g orders p ∧
      ∃ D : Set P.domain.carrier, ∃ hD : IsConvexFuchsianPolygon P D,
        Nat.card (OriginalRefinedSide hD) = 4 * g + 2 * (orders.length + p) - 2 := by
  let ms := orders ++ List.replicate (p - 1) 0
  have hms : ∀ m ∈ ms, m = 0 ∨ 2 ≤ m :=
    cofinite_cusped_order_list_allowed orders p horders
  have hdef' : 0 < cofiniteConstructionDeficit g ms 0 := by
    rw [cofiniteConstruction_cusped_orders_deficit g orders p horders hp]
    exact hdef
  obtain ⟨d, hd, hb⟩ := cofiniteConstruction_radius_exists g ms 0 hms (Or.inl rfl) hdef'
  let θ : Fin (cofiniteConstructionAngles g ms 0).length → ℝ :=
    fun i => (cofiniteConstructionAngles g ms 0)[i]
  let hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi := fun i =>
    cofiniteConstruction_angles_mem g ms 0 hms (Or.inl rfl) hdef' _ (List.getElem_mem i.isLt)
  let ρ := cofiniteConstructionPairing g ms 0
  let hρ := cofiniteConstructionPairing_involutive g ms 0
  let hθρ := cofiniteConstructionPairing_angle_profile g ms 0
  let hPeriod := cofiniteConstruction_mixed_angular_periods g ms 0 hms (Or.inl rfl) hdef'
  let H := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
    (cofiniteConstructionCuspedMobiusGroup g ms hms hdef' d hd hb)
  let P₀ := cofiniteConstructionCuspedHalfPlaneData g ms hms hdef' d hd hb
  let P := P₀.cayleyData
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let D := P₀.cayleyCoordinate '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.interior Q)
  have hD : IsConvexFuchsianPolygon P D :=
    cofiniteMixedTangential_projective_disc_convex θ d hθ hd hb ρ hρ hθρ hPeriod
  have hSig : HasCofiniteFuchsianSignature P.asFuchsianDisc g orders p := by
    have hs := cofiniteConstruction_cusped_actual_signature g ms hms hdef' d hd hb
    have hf : ms.filter (fun m => m ≠ 0) = orders := cofinite_cusped_order_list_filter orders p horders
    have hc : 1 + ms.count 0 = p := cofinite_cusped_order_list_cusp_count orders p horders hp
    rw [hf, hc] at hs
    exact hs
  let a : Fin (4 * g + ms.length) := ⟨0, by
    have hB := cofiniteConstruction_base_count g ms 0 hdef'
    omega⟩
  let i := cofiniteConstructionBaseIndex g ms 0 a
  have hi : θ i = 0 := by
    change (cofiniteConstructionAngles g ms 0)[cofiniteConstructionBaseIndex g ms 0 a] = 0
    rw [cofiniteConstructionBaseIndex_angle]
    simp only [cofiniteConstructionBaseAngle, cofiniteConstructionConeAngle, Nat.cast_zero, div_zero, zero_div]
  have hfirst : P.asFuchsianDisc.IsFirstKind :=
    cofiniteMixedTangential_firstKind_of_zero θ d hθ hd hb ρ hρ hθρ hPeriod i hi
  refine ⟨H, P, cofiniteMixedTangential_finitelyGenerated θ d hθ hd hb ρ hρ hθρ hPeriod,
    hfirst, hSig, D, hD, ?_⟩
  have hcount := cofiniteConstruction_mixed_actual_refined_side_count g ms 0 hms (Or.inl rfl) hdef' d hd hb
  change Nat.card (OriginalRefinedSide hD) = 4 * g + 2 * ms.length at hcount
  have hlen : ms.length = orders.length + (p - 1) := cofinite_cusped_order_list_length orders p
  rw [hcount, hlen]
  omega

end LowDimensionalTopology.Geometry.Fuchsian
