module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannSphereTopology
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscCyclicGroups
public import LowDimensionalTopology.Geometry.Surfaces.Topology.TorusFundamentalGroup
@[expose] public section
noncomputable section
open Set Topology
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A surface with the topology of the actual two-torus cannot be a no-elliptic
hyperbolic disc quotient: its genuine Z x Z deck group would have to be cyclic. -/
theorem riemannSurface_not_hyperbolicType_of_homeomorphic_torus {X : Type*}
    [TopologicalSpace X] (R : RiemannSurface X) (e : X ≃ₜ ComplexTorusCarrier) :
    ¬IsHyperbolicType R := by
  rintro ⟨H, hInv, hD, hno, f, hf, hbij⟩
  let D := unitDiscMobiusInvariantDomain H hInv
  let E := hf.toHomeomorph hbij
  let Et : MobiusDomainQuotient D ≃ₜ ComplexTorusCarrier := E.symm.trans e
  let z : D.carrier := Classical.choice inferInstance
  let x := mobiusDomainProjection D z
  let : SimplyConnectedSpace D.carrier := discRiemannSurface_simplyConnected
  let hp := mobiusDomain_noElliptic_covering D hD hno
  let j : Hᵐᵒᵖ ≃* Multiplicative ℤ × Multiplicative ℤ :=
    (hp.fundamentalGroupEquiv (x := x) ⟨z, rfl⟩).symm.trans
      ((fundamentalGroupHomeomorphMulEquiv Et x).trans (torusProductFundamentalGroupEquiv (Et x)))
  let jH : H ≃* Multiplicative ℤ × Multiplicative ℤ := {
    toEquiv := MulOpposite.opEquiv.trans j.toEquiv
    map_mul' := by
      intro a b
      change j (MulOpposite.op (a * b)) = j (MulOpposite.op a) * j (MulOpposite.op b)
      rw [MulOpposite.op_mul, map_mul, mul_comm] }
  have hcomm (a b : H) : Commute a b := by
    change a * b = b * a
    apply jH.injective
    rw [map_mul, map_mul, mul_comm]
  have hdisc : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H := by
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc, ?_⟩
    intro g
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hInv g w hw
    · intro w hw
      exact ⟨g⁻¹ • w, hInv g⁻¹ w hw, smul_inv_smul g w⟩
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete H D.carrier D.invariant
      D.isConnected.nonempty hD
  have hn : ∀ g ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g := fun g hg he => hno g hg he.1 he
  have hc := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_abelian_noElliptic_invariantDisc_isCyclic H hd hdisc hcomm hn
  exact not_isCyclic_prod_of_infinite_nontrivial (Multiplicative ℤ) (Multiplicative ℤ)
    (jH.isCyclic.mp hc)

theorem RiemannConformallyEquivalent.not_sphere_of_homeomorphic_torus {X : Type*}
    [TopologicalSpace X] (R : RiemannSurface X) (e : X ≃ₜ ComplexTorusCarrier) :
    ¬RiemannConformallyEquivalent R sphereRiemannSurface := by
  rintro ⟨f, hf, hbij⟩
  let := riemannSphere_simplyConnected
  let : SimplyConnectedSpace ComplexTorusCarrier :=
    (e.symm.trans (hf.toHomeomorph hbij)).toHomotopyEquiv.simplyConnectedSpace
  exact torusProductFundamentalGroup_not_isCyclic 0 inferInstance

/-- The genuine universal cover of any Riemann surface with the topology of the
two-torus is analytically the complex plane. -/
theorem RiemannUniversalCover.plane_model_of_homeomorphic_torus {X : Type*}
    [TopologicalSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R)
    (e : X ≃ₜ ComplexTorusCarrier) :
    @RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface complexPlaneRiemannSurface := by
  rcases C.uniformization with h | h | h
  · exact (riemannSurface_not_hyperbolicType_of_homeomorphic_torus R e
      (C.isHyperbolicType_of_conformallyEquivalent_disc h)).elim
  · exact h
  · exact (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.not_sphere_of_homeomorphic_torus
    R e
      (C.conformallyEquivalent_sphere_of_sphere_model h)).elim

/-- For compact original surfaces, the literal torus topology is exactly the
plane universal-cover alternative. -/
theorem RiemannUniversalCover.plane_model_iff_homeomorphic_torus {X : Type*}
    [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R) :
    @RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface complexPlaneRiemannSurface ↔
      Nonempty (X ≃ₜ ComplexTorusCarrier) := by
  constructor
  · intro h
    obtain ⟨b, T, f, hf, hbij⟩ := C.compact_plane_model_torus h
    exact ⟨hf.toHomeomorph hbij⟩
  · rintro ⟨e⟩
    exact C.plane_model_of_homeomorphic_torus e

theorem RiemannUniversalCover.projection_injective_of_base_simplyConnected {X : Type*}
    [TopologicalSpace X] [SimplyConnectedSpace X] {R : RiemannSurface X}
    (C : RiemannUniversalCover R) : Function.Injective C.projection := by
  let := C.topology
  let := C.simplyConnected
  let : LocallyPathConnectedSpace X := R.toRiemannAtlas.locallyPathConnectedSpace
  let c : C.space := Classical.choice inferInstance
  obtain ⟨F, ⟨hFc, hpF⟩, _⟩ := C.covering.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) (C.projection c) c rfl
  have hFp : (F : X → C.space) ∘ C.projection = id := by
    apply C.covering.eq_of_comp_eq (F.continuous.comp C.covering.continuous) continuous_id
    · funext y
      exact congrFun hpF (C.projection y)
    · exact hFc
  intro a b hab
  have ha := congrFun hFp a
  have hb := congrFun hFp b
  change F (C.projection a) = a at ha
  change F (C.projection b) = b at hb
  exact ha.symm.trans ((congrArg F hab).trans hb)


/-- The actual sphere universal-cover alternative is exactly the sphere topology
of the original base. -/
theorem RiemannUniversalCover.sphere_model_iff_homeomorphic_sphere {X : Type*}
    [TopologicalSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R) :
    @RiemannConformallyEquivalent C.space (OnePoint ℂ) C.topology _ C.surface
      sphereRiemannSurface ↔ Nonempty (X ≃ₜ OnePoint ℂ) := by
  constructor
  · intro h
    exact riemannSurface_conformallyEquivalent_sphere_iff_homeomorphic_sphere R |>.mp
      (C.conformallyEquivalent_sphere_of_sphere_model h)
  · rintro ⟨e⟩
    let := C.topology
    let := riemannSphere_simplyConnected
    let : SimplyConnectedSpace X := e.toHomotopyEquiv.simplyConnectedSpace
    have hCX : RiemannConformallyEquivalent C.surface R :=
      ⟨C.projection, C.analytic_projection,
        C.projection_injective_of_base_simplyConnected, C.surjective⟩
    exact hCX.trans (riemannSurface_conformallyEquivalent_sphere_iff_homeomorphic_sphere R |>.mpr
      ⟨e⟩)

/-- For compact surfaces, the actual disc-cover alternative is precisely the
remaining topological case after the literal sphere and two-torus. -/
theorem RiemannUniversalCover.disc_model_iff_not_sphere_not_torus {X : Type*}
    [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R) :
    @RiemannConformallyEquivalent C.space _ C.topology _ C.surface discRiemannSurface ↔
      (¬Nonempty (X ≃ₜ OnePoint ℂ)) ∧ (¬Nonempty (X ≃ₜ ComplexTorusCarrier)) := by
  let := C.topology
  constructor
  · intro h
    constructor
    · intro he
      have hs := C.sphere_model_iff_homeomorphic_sphere.mpr he
      exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.not_disc_of_compact sphereRiemannSurface
        (hs.symm.trans h)
    · rintro ⟨e⟩
      exact riemannSurface_not_hyperbolicType_of_homeomorphic_torus R e
        (C.isHyperbolicType_of_conformallyEquivalent_disc h)
  · rintro ⟨hs, ht⟩
    rcases C.uniformization with h | h | h
    · exact h
    · exact (ht (C.plane_model_iff_homeomorphic_torus.mp h)).elim
    · exact (hs (C.sphere_model_iff_homeomorphic_sphere.mp h)).elim

end LowDimensionalTopology.Geometry.Surfaces
