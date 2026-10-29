module

public import LowDimensionalTopology.Geometry.Fuchsian.PantsSignatureCappedComplement
public import LowDimensionalTopology.Geometry.Surfaces.Topology.StandardPantsSphereCapComplement
public import LowDimensionalTopology.Geometry.Surfaces.Topology.ThreeSphericalDiscs
public import Mathlib.Data.Fintype.EquivFin

/-!
# The actual three-end Nielsen core has the literal planar pants type

The only outstanding input is the explicitly named finite marked-disc theorem
on the two-sphere. All physical caps and their open-core complement come from
the original group's actual capped realization and its actual signature.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Unproved.Surfaces

/-- Subject to the explicit independent three-disc theorem, the original open
Nielsen core of the actual three-boundary signature has the literal pants type. -/
theorem threeBoundaryOpenCore_homeomorphic_pantsPlanarRegion
    (hHard : ThreeSphericalDiscs)
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {hNE : DiscreteGroups.IsNonElementary H} {hFG : H.FG}
    (h : HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3) :
    Nonempty (threeBoundaryOpenCore P hNE ≃ₜ Surfaces.pantsPlanarRegion) := by
  classical
  obtain ⟨w, hw, hwN, J, hc, hv, _n, S, hr, ⟨eW⟩, hcard, ⟨eCore⟩⟩ :=
    h.openCore_capped_complement
  let hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin := finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD := dirichletDomain_center_mem P w hw
  let Pcap := nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
  let A := {f : Pcap.Face //
    f ≠ nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
  let capA := fun f : A => nielsenActualCapDisc hD hNE hFG hfin w hwD hwN J hc hv f
  have hcount : Fintype.card A = 3 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let index : Fin 3 ≃ A := (Fintype.equivFinOfCardEq hcount).symm
  let cap : Fin 3 → Complex.UnitClosedDisc → SphericalDiscSphere :=
    fun i z => eW (capA (index i) z)
  have hcap (i : Fin 3) : Topology.IsEmbedding (cap i) :=
    eW.isEmbedding.comp
      (nielsenActualCapDisc_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv (index i)).isEmbedding
  have hA : Pairwise (fun f g : A => Disjoint (range (capA f)) (range (capA g))) := by
    simpa only [capA, nielsenActualCapDisc_range] using
      nielsenCappedClosedCap_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv
  have hcapDisjoint : Pairwise (fun i j : Fin 3 => Disjoint (range (cap i)) (range (cap j))) := by
    intro i j hij
    change Disjoint (range (eW ∘ capA (index i))) (range (eW ∘ capA (index j)))
    rw [Set.range_comp, Set.range_comp]
    exact Set.disjoint_image_of_injective eW.injective (hA (fun he => hij (index.injective he)))
  have hUnion : eW '' (⋃ f : A, range (capA f)) = ⋃ i : Fin 3, range (cap i) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨f, z, hz⟩ := mem_iUnion.mp hx
      obtain ⟨i, rfl⟩ := index.surjective f
      exact mem_iUnion.mpr ⟨i, z, congrArg eW hz⟩
    · intro hy
      obtain ⟨i, z, hz⟩ := mem_iUnion.mp hy
      exact ⟨capA (index i) z, mem_iUnion.mpr ⟨index i, z, rfl⟩, hz⟩
  let eTransport : ↥((⋃ f : A, range (capA f))ᶜ) ≃ₜ
      ↥((⋃ i : Fin 3, range (cap i))ᶜ) :=
    (eW.image _).trans (Homeomorph.setCongr (by rw [eW.image_compl, hUnion]))
  let eMatch := Surfaces.threeSphericalDiscComplementsHomeomorph hHard cap
    Surfaces.pantsStandardSphereCap hcap
    (fun i => (Surfaces.pantsStandardSphereCap_isClosedEmbedding i).isEmbedding)
    hcapDisjoint Surfaces.pantsStandardSphereCap_pairwise_disjoint
  exact ⟨eCore.trans (eTransport.trans
    (eMatch.trans Surfaces.pantsStandardSphereComplementHomeomorph))⟩

end LowDimensionalTopology.Geometry.Fuchsian
