/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ReflectionProductTraces
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicRays
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.ParabolicPencilTransport
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.DiscIsometricBisectors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Every moved interior point lies on a genuine member of the actual associated pencil. -/
theorem hAssociatedPencil_exists_through (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : ℍ) (hw : A • w≠w) : ∃ L : HalfPlaneLine,L∈hAssociatedPencil A ∧ w∈L.carrier := by
  have hA : realSLMobius A≠1 := by
    intro he
    apply hw
    apply UpperHalfPlane.coe_injective
    apply OnePoint.coe_injective
    rw [←realSLMobius_action,he]
    rfl
  rcases lt_trichotomy ((Matrix.trace A.val)^2) 4 with ht | ht | ht
  · have hE := (realSLMobius_elliptic_iff A hA).mpr ht
    let v := hEllipticCenter A ht
    have hvw : v≠w := by
      intro he
      apply hw
      exact (hSL_elliptic_fixed_iff A ht w).mpr he.symm
    obtain ⟨L,hv,hLw⟩ := exists_halfPlaneLine_through v w hvw
    exact ⟨L,Or.inl ⟨hE,hv⟩,hLw⟩
  · have hP := (realSLMobius_parabolic_iff A hA).mpr ht
    have hp := realSLMobius_parabolic_fixed_boundary A hP _ (hParabolicIdealPoint_fixed A hP)
    obtain ⟨L,hwL,hpL⟩ := exists_halfPlaneLine_through_point_and_idealEndpoint w (hParabolicIdealPoint A hP) hp
    exact ⟨L,Or.inr (Or.inl ⟨hP,hpL⟩),hwL⟩
  · let axis := hHyperbolicAxis A hA ht
    obtain ⟨L,⟨hwL,hO⟩,_⟩ := axis.existsUnique_perpendicular w
    exact ⟨L,Or.inr (Or.inr ⟨hA,ht,axis.orthogonal_symm L hO⟩),hwL⟩

/-- A genuine line reflection exchanging distinct points has their full genuine equidistance locus as axis. -/
theorem HalfPlaneLine.carrier_eq_equidistant_of_reflection_swap (L : HalfPlaneLine)
    (a b : ℍ) (hab : a≠b) (hswap : L.reflection a=b) : L.carrier=HEquidistantLocus a b := by
  obtain ⟨N,hN⟩ := exists_hEquidistantLine hab
  have hsub : L.carrier⊆N.carrier := by
    intro z hz
    rw [hN]
    change dist z a=dist z b
    have hfix := (L.reflection_fixed_iff z).mpr hz
    calc
      dist z a=dist (L.reflection z) (L.reflection a) := (L.reflection_isometry.dist_eq z a).symm
      _=dist z b := by rw [hfix,hswap]
  obtain ⟨x,y,hx,hy,hxy⟩ := L.exists_two_points
  have he := L.eq_of_two_points N hxy hx hy (hsub hx) (hsub hy)
  rw [he,hN]

/-- The intrinsic geometric w-isometric line for an actual native interior point. -/
def hWIsometricCircle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℍ) : Set ℍ :=
  HEquidistantLocus w (A⁻¹ • w)

/-- The intrinsic interior definition is exactly the source reflection-factor construction. -/
theorem existsUnique_hWIsometricCircle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (w : ℍ) (hw : A • w≠w) :
    ∃! M : HalfPlaneLine,M.carrier=hWIsometricCircle A w ∧
      ∃ L : HalfPlaneLine,w∈L.carrier ∧ (A • · : ℍ→ℍ)=L.reflection ∘ M.reflection := by
  obtain ⟨L,hLA,hwL⟩ := hAssociatedPencil_exists_through A w hw
  obtain ⟨M,hM⟩ := hAssociatedPencil_factor_right A L hLA
  have hwv : w≠A⁻¹ • w := by
    intro he
    have hh := congrArg (fun z : ℍ=>A • z) he
    rw [smul_inv_smul] at hh
    exact hw hh
  have hAw : A • M.reflection w=w := by
    rw [congrFun hM]
    change L.reflection (M.reflection (M.reflection w))=w
    rw [M.reflection_involutive,(L.reflection_fixed_iff w).mpr hwL]
  have hswap : M.reflection w=A⁻¹ • w := by
    have he := congrArg (fun z : ℍ=>A⁻¹ • z) hAw
    simpa only [inv_smul_smul] using he
  have hcar := M.carrier_eq_equidistant_of_reflection_swap w (A⁻¹ • w) hwv hswap
  refine ⟨M,⟨hcar,L,hwL,hM⟩,?_⟩
  intro N hN
  exact HalfPlaneLine.carrier_injective (hN.1.trans hcar.symm)

/-- Actual conjugacy covariance of the complete interior w-isometric line. -/
theorem hWIsometricCircle_conjugation (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℍ) :
    hWIsometricCircle (q*A*q⁻¹) (q • w)=(q • · : ℍ→ℍ) '' hWIsometricCircle A w := by
  unfold hWIsometricCircle
  have he : (q*A*q⁻¹)⁻¹ • (q • w)=q • (A⁻¹ • w) := by simp only [mul_inv_rev,inv_inv,mul_smul,inv_smul_smul]
  rw [he]
  exact hEquidistantLocus_realGL_image (Matrix.SpecialLinearGroup.mapGL ℝ q) w (A⁻¹ • w)

/-- The classical circle of the original map is the bisector of the origin and its actual inverse image. -/
theorem disc_classical_isometricCircle_inverse_bisector (a c : ℂ)
    (h : ‖a‖^2-‖c‖^2=1) (hc : c≠0) :
    {z : 𝔻 | (z : ℂ)∈Mobius.isometricCircle a (conj c) c (conj a)}=
      DiscEquidistantLocus 0 (discCoefficientAction (conj a) (-c) (disc_coefficient_inverse_unit a c h) 0) := by
  have he := discCoefficientAction_bisector_isometricCircle (disc_coefficient_inverse_unit a c h) (neg_ne_zero.mpr hc)
  simpa only [map_neg,Complex.conj_conj,neg_neg] using he.symm

/-- The classical formula with the geometric condition that the original map moves the base point. -/
theorem disc_classical_isometricCircle_inverse_bisector_of_origin_ne (a c : ℂ)
    (h : ‖a‖^2-‖c‖^2=1) (h0 : discCoefficientAction a c h 0≠0) :
    {z : 𝔻 | (z : ℂ)∈Mobius.isometricCircle a (conj c) c (conj a)}=
      DiscEquidistantLocus 0 (discCoefficientAction (conj a) (-c) (disc_coefficient_inverse_unit a c h) 0) := by
  have hc : c≠0 := by
    intro hc
    apply h0
    apply Complex.UnitDisc.coe_injective
    simp [discCoefficientAction_coe,hc]
  exact disc_classical_isometricCircle_inverse_bisector a c h hc

end LowDimensionalTopology.Geometry.Hyperbolic
