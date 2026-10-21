module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteBranchProfiles
public import Mathlib.GroupTheory.SpecificGroups.Alternating
@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius

/-- A vertex with stabilizer order three has four actual orbit points in an order-twelve group. -/
theorem finiteMobius_tetrahedral_orbit_card (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hH : Nat.card H = 12)
    (hz : Nat.card (MulAction.stabilizer H z) = 3) : Nat.card (MulAction.orbit H z) = 4 := by
  have he := finiteMobius_vertex_orbit_stabilizer H z
  rw [hH, hz] at he
  omega

/-- Labeling an actual four-point orbit, without assuming a faithful abstract action. -/
def finiteMobius_fourOrbitEquiv (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hz : Nat.card (MulAction.orbit H z) = 4) :
    MulAction.orbit H z ≃ Fin 4 := by
  letI : Fintype (MulAction.orbit H z) := Fintype.ofFinite _
  exact Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hz)

/-- The actual Mobius action, transported to labels of the four actual orbit points. -/
def finiteMobius_fourOrbitHom (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hz : Nat.card (MulAction.orbit H z) = 4) : H →* Equiv.Perm (Fin 4) :=
  (finiteMobius_fourOrbitEquiv H z hz).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom H (MulAction.orbit H z))

/-- The degree-four representation is faithful because a nonidentity Mobius map has only two fixed points. -/
theorem finiteMobius_fourOrbitHom_injective (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hz : Nat.card (MulAction.orbit H z) = 4) :
    Function.Injective (finiteMobius_fourOrbitHom H z hz) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have he : MulAction.toPermHom H (MulAction.orbit H z) g = 1 := by
    apply (finiteMobius_fourOrbitEquiv H z hz).permCongrHom.injective
    change (finiteMobius_fourOrbitEquiv H z hz).permCongrHom
      (MulAction.toPermHom H (MulAction.orbit H z) g) = 1 at hg
    simpa only [map_one] using hg
  have hfix (x : MulAction.orbit H z) : g • x.val = x.val := by
    exact congrArg Subtype.val (congrArg (fun p : Equiv.Perm (MulAction.orbit H z) => p x) he)
  by_contra hne
  let F : MulAction.orbit H z → MulAction.fixedBy (MobiusVertex H) g :=
    fun x => ⟨x.val, hfix x⟩
  have hF : Function.Injective F := by
    intro a b hab
    exact Subtype.ext (congrArg
      (fun x : MulAction.fixedBy (MobiusVertex H) g => x.val) hab)
  have hc := Nat.card_le_card_of_injective F hF
  rw [hz, finiteMobius_vertex_fixedBy_card H g hne] at hc
  omega

/-- The faithful image has the true group order. -/
theorem finiteMobius_fourOrbitHom_range_card (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hz : Nat.card (MulAction.orbit H z) = 4) :
    Nat.card (finiteMobius_fourOrbitHom H z hz).range = Nat.card H :=
  Nat.card_congr (MonoidHom.ofInjective (finiteMobius_fourOrbitHom_injective H z hz)).toEquiv.symm

/-- In the tetrahedral profile the actual degree-four image has index two in S4. -/
theorem finiteMobius_tetrahedral_image_index (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hz : Nat.card (MulAction.orbit H z) = 4)
    (hH : Nat.card H = 12) : (finiteMobius_fourOrbitHom H z hz).range.index = 2 := by
  have he := (finiteMobius_fourOrbitHom H z hz).range.index_mul_card
  rw [finiteMobius_fourOrbitHom_range_card H z hz, hH] at he
  have hp : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [hp] at he
  omega

/-- The actual image is all of A4, rather than a chosen abstract copy supplied as a hypothesis. -/
theorem finiteMobius_tetrahedral_image_eq_alternating (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hz : Nat.card (MulAction.orbit H z) = 4)
    (hH : Nat.card H = 12) :
    (finiteMobius_fourOrbitHom H z hz).range = alternatingGroup (Fin 4) :=
  Equiv.Perm.eq_alternatingGroup_of_index_eq_two (finiteMobius_tetrahedral_image_index H z hz hH)

/-- The tetrahedral case isomorphism is induced by the true boundary orbit action. -/
def finiteMobius_tetrahedralEquiv_of_vertex (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hH : Nat.card H = 12)
    (hz : Nat.card (MulAction.stabilizer H z) = 3) : H ≃* alternatingGroup (Fin 4) :=
  (MonoidHom.ofInjective (finiteMobius_fourOrbitHom_injective H z
    (finiteMobius_tetrahedral_orbit_card H z hH hz))).trans
    (MulEquiv.subgroupCongr (finiteMobius_tetrahedral_image_eq_alternating H z
      (finiteMobius_tetrahedral_orbit_card H z hH hz) hH))

/-- finite tetrahedral case: the actual numerical branch profile yields A4. -/
def finiteMobius_tetrahedralEquiv (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (e : Fin 3 ≃ MobiusVertexOrbit H)
    (hp : (Nat.card H, mobiusVertexBranchOrder H (e 0), mobiusVertexBranchOrder H (e 1),
      mobiusVertexBranchOrder H (e 2)) = (12, 2, 3, 3)) : H ≃* alternatingGroup (Fin 4) := by
  have hH : Nat.card H = 12 := congrArg Prod.fst hp
  have hz : Nat.card (MulAction.stabilizer H (e 1).out) = 3 :=
    congrArg (fun t : ℕ × ℕ × ℕ × ℕ => t.2.2.1) hp
  exact finiteMobius_tetrahedralEquiv_of_vertex H (e 1).out hH hz

/-- Evaluation of the permutation is the transported actual orbit action. -/
theorem finiteMobius_fourOrbitHom_apply (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hz : Nat.card (MulAction.orbit H z) = 4) (g : H) (i : Fin 4) :
    finiteMobius_fourOrbitHom H z hz g i = finiteMobius_fourOrbitEquiv H z hz
      (g • (finiteMobius_fourOrbitEquiv H z hz).symm i) := rfl

/-- On the underlying genuine complex boundary points, the degree-four action is exactly the original map. -/
theorem finiteMobius_fourOrbitHom_boundary_action (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hz : Nat.card (MulAction.orbit H z) = 4) (g : H) (i : Fin 4) :
    (((finiteMobius_fourOrbitEquiv H z hz).symm (finiteMobius_fourOrbitHom H z hz g i)).val :
      Mobius.ExtendedComplex) = (g.val : Equiv.Perm Mobius.ExtendedComplex)
        (((finiteMobius_fourOrbitEquiv H z hz).symm i).val : Mobius.ExtendedComplex) := by
  rw [finiteMobius_fourOrbitHom_apply, Equiv.symm_apply_apply]
  rfl

/-- The alternating-group identification retains precisely the faithful four-point permutation. -/
theorem finiteMobius_tetrahedralEquiv_of_vertex_coe (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) (hH : Nat.card H = 12)
    (hz : Nat.card (MulAction.stabilizer H z) = 3) (g : H) :
    (finiteMobius_tetrahedralEquiv_of_vertex H z hH hz g : Equiv.Perm (Fin 4)) =
      finiteMobius_fourOrbitHom H z (finiteMobius_tetrahedral_orbit_card H z hH hz) g := rfl

end LowDimensionalTopology.Geometry.DiscreteGroups
