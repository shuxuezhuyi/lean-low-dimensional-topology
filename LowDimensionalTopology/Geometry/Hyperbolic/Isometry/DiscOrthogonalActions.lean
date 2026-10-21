/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteDihedralSectors
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteDihedralGroups
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteDihedralChambers
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import Mathlib.Analysis.SpecialFunctions.Arcosh
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A genuine real-linear planar isometry restricts to the actual open unit disc. -/
def discOrthogonalMap (L : ℂ ≃ₗᵢ[ℝ] ℂ) (z : 𝔻) : 𝔻 :=
  Complex.UnitDisc.mk (L (z:ℂ)) (by rw [L.norm_map];exact z.norm_lt_one)

theorem discOrthogonalMap_coe (L : ℂ ≃ₗᵢ[ℝ] ℂ) (z : 𝔻) :
    (discOrthogonalMap L z:ℂ)=L (z:ℂ) := rfl

theorem discOrthogonalMap_pathDist (L : ℂ ≃ₗᵢ[ℝ] ℂ) (z w : 𝔻) :
    discPathDist (discOrthogonalMap L z) (discOrthogonalMap L w)=discPathDist z w := by
  apply Real.cosh_injOn
  · rw [discPathDist_eq_halfPlane];exact dist_nonneg
  · rw [discPathDist_eq_halfPlane];exact dist_nonneg
  · rw [disc_cosh_distance,disc_cosh_distance]
    simp only [discOrthogonalMap_coe,←map_sub,L.norm_map]

local instance discOrthogonalHyperbolicMetric : MetricSpace 𝔻:=discHyperbolicMetric

/-- This is an isometry for the independently proved original weighted-path metric. -/
def discOrthogonalIsometry (L : ℂ ≃ₗᵢ[ℝ] ℂ) : 𝔻 ≃ᵢ 𝔻 where
  toFun:=discOrthogonalMap L
  invFun:=discOrthogonalMap L.symm
  left_inv:=by intro z;apply Subtype.ext;exact L.symm_apply_apply (z:ℂ)
  right_inv:=by intro z;apply Subtype.ext;exact L.apply_symm_apply (z:ℂ)
  isometry_toFun:=by
    apply Isometry.of_dist_eq
    intro z w
    change dist (discToHalfPlane (discOrthogonalMap L z))
      (discToHalfPlane (discOrthogonalMap L w))=dist (discToHalfPlane z) (discToHalfPlane w)
    simpa only [←discPathDist_eq_halfPlane] using discOrthogonalMap_pathDist L z w

theorem discOrthogonalMap_zero (L : ℂ ≃ₗᵢ[ℝ] ℂ) : discOrthogonalMap L 0=0 := by
  apply Subtype.ext
  exact L.map_zero

theorem discOrthogonalIsometry_mul (L M : ℂ ≃ₗᵢ[ℝ] ℂ) :
    discOrthogonalIsometry (L*M)=discOrthogonalIsometry L*discOrthogonalIsometry M := by
  apply IsometryEquiv.ext
  intro z
  rfl

theorem discOrthogonalIsometry_one : discOrthogonalIsometry 1=1 := by
  apply IsometryEquiv.ext
  intro z
  rfl

/-- Restriction is a genuine homomorphism between the actual transformation groups. -/
def discOrthogonalHom : (ℂ ≃ₗᵢ[ℝ] ℂ)→* (𝔻 ≃ᵢ 𝔻) where
  toFun:=discOrthogonalIsometry
  map_one':=discOrthogonalIsometry_one
  map_mul':=discOrthogonalIsometry_mul

/-- The genuine finite angular maps preserve each actual hyperbolic disc ball about zero. -/
theorem discOrthogonalIsometry_ball (L : ℂ ≃ₗᵢ[ℝ] ℂ) (r : ℝ) :
    discOrthogonalIsometry L '' Metric.ball (0:𝔻) r=Metric.ball (0:𝔻) r := by
  simpa only [show discOrthogonalIsometry L 0=0 from discOrthogonalMap_zero L] using
    (discOrthogonalIsometry L).image_ball (0:𝔻) r

/-- The actual closed angular chamber inside the native hyperbolic disc. -/
def discDihedralChamber (n : ℕ) : Set 𝔻 :=
  {z | (z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (2*n)}

def discDihedralOpenChamber (n : ℕ) : Set 𝔻 :=
  {z | (z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector (2*n)}

def discDihedralAction (n : ℕ) (i : Fin n) (b : Bool) : 𝔻 ≃ᵢ 𝔻 :=
  discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^i.val) b)

theorem discDihedralAction_coe (n : ℕ) (i : Fin n) (b : Bool) (z : 𝔻) :
    (discDihedralAction n i b z:ℂ)=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteDihedralPlaneAction n i b (z:ℂ) := by
  cases b <;> rfl

/-- The finite actual angular pieces tile every genuine hyperbolic ball about zero. -/
theorem discDihedral_closed_chamber_ball_cover (n : ℕ) (hn : 0<n) (r : ℝ) :
    (⋃(i : Fin n)(b : Bool),discDihedralAction n i b ''
      (discDihedralChamber n∩Metric.ball (0:𝔻) r))=Metric.ball (0:𝔻) r := by
  ext z
  constructor
  · intro hz
    obtain ⟨i,hz⟩:=mem_iUnion.mp hz
    obtain ⟨b,v,⟨_,hv⟩,rfl⟩:=mem_iUnion.mp hz
    rw [←discOrthogonalIsometry_ball (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap
      (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^i.val) b) r]
    exact mem_image_of_mem _ hv
  · intro hz
    have hzC : (z:ℂ)∈⋃(i : Fin n)(b :
      Bool),_root_.LowDimensionalTopology.Geometry.Euclidean.finiteDihedralPlaneAction n i b ''
        _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (2*n):=by rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteDihedral_closedPlaneSector_finite_cover n hn];trivial
    obtain ⟨i,hzC⟩:=mem_iUnion.mp hzC
    obtain ⟨b,w,hw,he⟩:=mem_iUnion.mp hzC
    have hw1 : ‖w‖<1:=by
      have hnw:=(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteDihedralPlaneAction_norm n i b
        w).symm.trans (congrArg norm he)
      rw [hnw]
      exact z.norm_lt_one
    let v : 𝔻:=Complex.UnitDisc.mk w hw1
    have heD : discDihedralAction n i b v=z:=by
      apply Subtype.ext
      change (discDihedralAction n i b v:ℂ)=(z:ℂ)
      rw [discDihedralAction_coe]
      exact he
    have hball : v∈Metric.ball (0:𝔻) r:=by
      have hd:=(discDihedralAction n i b).dist_eq v (0:𝔻)
      have hzero : discDihedralAction n i b 0=0:=discOrthogonalMap_zero _
      rw [heD,hzero] at hd
      change dist v 0<r
      rw [←hd]
      exact hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨b,v,⟨hw,hball⟩,heD⟩⟩

/-- The native ball chambers retain disjoint genuine open interiors. -/
theorem discDihedral_open_chamber_disjoint (n : ℕ) (hn : 0<n) :
    Pairwise (fun a b : Fin n×Bool=>Disjoint
      (discDihedralAction n a.1 a.2 '' discDihedralOpenChamber n)
      (discDihedralAction n b.1 b.2 '' discDihedralOpenChamber n)) := by
  intro a b hab
  apply disjoint_left.mpr
  rintro z ⟨v,hv,hvz⟩ ⟨w,hw,hwz⟩
  apply disjoint_left.mp (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteDihedral_openPlaneSector_finite_disjoint n hn hab)
  · exact ⟨(v:ℂ),hv,(discDihedralAction_coe n a.1 a.2 v).symm.trans (congrArg Subtype.val hvz)⟩
  · exact ⟨(w:ℂ),hw,(discDihedralAction_coe n b.1 b.2 w).symm.trans (congrArg Subtype.val hwz)⟩

/-- The image is an actual finite subgroup of genuine native hyperbolic isometries. -/
def discDihedralGroup (n : ℕ) : Subgroup (𝔻 ≃ᵢ 𝔻) :=
  (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarDihedralGroup n).map discOrthogonalHom

theorem discDihedralGroup_finite (n : ℕ) (hn : 0<n) :
    (discDihedralGroup n : Set (𝔻 ≃ᵢ 𝔻)).Finite :=
  (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarDihedralGroup_finite n hn).image discOrthogonalHom

theorem discDihedralGroup_normal_form (n : ℕ) (hn : 0<n) (g : 𝔻 ≃ᵢ 𝔻)
    (hg : g∈discDihedralGroup n) : ∃i : Fin n,∃b : Bool,g=discDihedralAction n i b := by
  obtain ⟨L,hL,rfl⟩:=hg
  obtain ⟨k,b,hg⟩:=_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarDihedralGroup_normal_form n L hL
  obtain ⟨i,hi⟩:=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_zpow_eq_fin n hn k
  exact ⟨i,b,by rw [hg,hi];rfl⟩

theorem discDihedralAction_mem (n : ℕ) (i : Fin n) (b : Bool) :
    discDihedralAction n i b∈discDihedralGroup n := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^i.val) b,?_,rfl⟩
  change _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n^i.val) b∈_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarDihedralGroup n
  simpa only [zpow_natCast] using _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarDihedralGroup_normal_form_mem n (i.val:ℤ) b

/-- Genuine native chamber coincidences are exactly the original boundary mirror identifications. -/
theorem discDihedral_chamber_coincidence (n : ℕ) (hn : 0<n)
    (g h : 𝔻 ≃ᵢ 𝔻) (hg : g∈discDihedralGroup n) (hh : h∈discDihedralGroup n)
    (x y : 𝔻) (hx : x∈discDihedralChamber n) (hy : y∈discDihedralChamber n)
    (he : g x=h y) :
    x=y ∧ (x=0 ∨ g=h ∨ ∃R : ℂ ≃ₗᵢ[ℝ] ℂ,
      (R=_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap 1 true ∨
        R=_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap
        (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) true) ∧
      discOrthogonalIsometry R x=x ∧ g=h*discOrthogonalIsometry R) := by
  obtain ⟨L,hL,rfl⟩:=hg
  obtain ⟨M,hM,rfl⟩:=hh
  have heC : L (x:ℂ)=M (y:ℂ):=congrArg Subtype.val he
  obtain ⟨hxy,hcases⟩:=_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarDihedral_chamber_coincidence n hn L M hL hM (x:ℂ) (y:ℂ) hx hy heC
  refine ⟨Subtype.ext hxy,?_⟩
  rcases hcases with hx0|heq|⟨R,hR,hfix,hg⟩
  · exact Or.inl (Subtype.ext hx0)
  · exact Or.inr (Or.inl (congrArg discOrthogonalHom heq))
  · right;right
    refine ⟨R,hR,Subtype.ext hfix,?_⟩
    exact congrArg discOrthogonalHom hg |>.trans (map_mul discOrthogonalHom M R)

end LowDimensionalTopology.Geometry.Hyperbolic
