/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Auxiliary.Topology.TopologicalGroup
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.OrbitQuotient
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Isometry

/-!
Topological preliminaries, equivalence quotients, homeomorphism-group
orbit quotients, singleton product, and normal-subgroup quotient conventions.
-/

@[expose] public section

open Topology

universe u v

namespace LowDimensionalTopology.Geometry.Auxiliary.Topology


variable {X : Type u} {Y : Type v}

noncomputable def compactHausdorffHomeomorph [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] (f : X → Y) (hf : Continuous f)
    (hbij : Function.Bijective f) : X ≃ₜ Y :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) hf

abbrev discreteTopology : TopologicalSpace X := ⊥

theorem isOpen_discreteTopology (s : Set X) : @IsOpen X discreteTopology s := by
  change True
  trivial

abbrev metricTopology [MetricSpace X] : TopologicalSpace X := inferInstance

theorem isOpen_metricTopology_iff [MetricSpace X] (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s := Metric.isOpen_iff

abbrev surjectiveIsometry [MetricSpace X] [MetricSpace Y] := X ≃ᵢ Y

noncomputable def surjectiveIsometryOfFunction [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hf : Isometry f) (hs : Function.Surjective f) : X ≃ᵢ Y :=
  { Equiv.ofBijective f ⟨hf.injective, hs⟩ with isometry_toFun := hf }

theorem surjectiveIsometryOfFunction_apply [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hf : Isometry f) (hs : Function.Surjective f) (x : X) :
    surjectiveIsometryOfFunction f hf hs x = f x := rfl

theorem surjectiveIsometry_dist [MetricSpace X] [MetricSpace Y]
    (f : surjectiveIsometry (X := X) (Y := Y)) (x y : X) : dist (f x) (f y) = dist x y :=
  f.isometry.dist_eq x y

def isometryHomeomorph [MetricSpace X] [MetricSpace Y]
    (f : surjectiveIsometry (X := X) (Y := Y)) : X ≃ₜ Y := f.toHomeomorph

theorem quotientProjection_continuous [TopologicalSpace X] (f : X → Y) :
    Continuous[inferInstance, quotientTopology f] f := continuous_coinduced_rng

abbrev equivalenceQuotient (r : Setoid X) := Quotient r

theorem equivalenceQuotient_topology [TopologicalSpace X] (r : Setoid X) :
    (inferInstance : TopologicalSpace (equivalenceQuotient r)) =
      quotientTopology (Quotient.mk r) := rfl

noncomputable def fiberQuotientEquiv (f : X → Y) (hf : Function.Surjective f) :
    Quotient (Setoid.ker f) ≃ Y := Setoid.quotientKerEquivOfSurjective f hf

theorem fiberQuotientEquiv_apply (f : X → Y) (hf : Function.Surjective f) (x : X) :
    fiberQuotientEquiv f hf (Quotient.mk (Setoid.ker f) x) = f x := rfl

noncomputable def fiberQuotientHomeomorph [TopologicalSpace X]
    (f : X → Y) (hf : Function.Surjective f) :
    @Homeomorph (Quotient (Setoid.ker f)) Y inferInstance (quotientTopology f) := by
  letI : TopologicalSpace Y := quotientTopology f
  refine { toEquiv := fiberQuotientEquiv f hf, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply continuous_coinduced_dom.mpr
    change Continuous[inferInstance, quotientTopology f] f
    exact continuous_coinduced_rng
  · apply continuous_coinduced_dom.mpr
    have he : (fiberQuotientEquiv f hf).symm ∘ f = Quotient.mk (Setoid.ker f) := by
      funext x
      apply (fiberQuotientEquiv f hf).injective
      simp only [Function.comp_apply, Equiv.apply_symm_apply, fiberQuotientEquiv_apply]
    change Continuous ((fiberQuotientEquiv f hf).symm ∘ f)
    rw [he]
    exact continuous_quot_mk

section OrbitQuotient

variable [TopologicalSpace X] (G : Subgroup (X ≃ₜ X))

abbrev homeomorphOrbitQuotient := DiscreteGroups.Action.orbitQuotient G X

theorem homeomorphOrbitProjection_continuous :
    Continuous (DiscreteGroups.Action.orbitProjection G X) := DiscreteGroups.Action.orbitProjection_continuous G X

theorem homeomorphOrbit_saturation (s : Set X) :
    DiscreteGroups.Action.orbitProjection G X ⁻¹' (DiscreteGroups.Action.orbitProjection G X '' s) =
      ⋃ g : G, (fun x : X => g • x) '' s :=
  MulAction.quotient_preimage_image_eq_union_mul s

theorem homeomorphOrbitProjection_open : IsOpenMap (DiscreteGroups.Action.orbitProjection G X) := by
  let : ContinuousConstSMul G X := ⟨fun g => g.val.continuous_toFun⟩
  exact DiscreteGroups.Action.orbitProjection_isOpenMap G X

end OrbitQuotient

def singletonProductHomeomorph [TopologicalSpace X] [TopologicalSpace Y] (y : Y) :
    X ≃ₜ X × ({y} : Set Y) where
  toFun := fun x => (x, ⟨y, rfl⟩)
  invFun := Prod.fst
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨x, z, hz⟩
    have he : z = y := hz
    subst z
    rfl
  continuous_toFun := continuous_id.prodMk continuous_const
  continuous_invFun := continuous_fst

abbrev normalSubgroupQuotient {G : Type*} [Group G] (N : Subgroup G) [N.Normal] := G ⧸ N

theorem normalSubgroupQuotient_topology {G : Type*} [Group G] [TopologicalSpace G]
    (N : Subgroup G) [N.Normal] :
    (inferInstance : TopologicalSpace (normalSubgroupQuotient N)) =
      quotientTopology (QuotientGroup.mk : G → G ⧸ N) := rfl

end LowDimensionalTopology.Geometry.Auxiliary.Topology
