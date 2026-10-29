/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.OriginalCanonicalFamily
public import LowDimensionalTopology.Geometry.Surfaces.Topology.GeneratorLoopTransport

/-!
# Closed surfaces with original geometric ordered markings

A marking consists of the actual based classes of an original oriented
canonical polygon cut, or the empty family in genus zero. An analytic
homeomorphism identifies two such marked surfaces when one common path
transports every corresponding ordered class. Their quotient retains the
original carriers and complex atlases.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

/-- A closed genus-g surface with an actual original geometric ordered
canonical family at one prescribed basepoint. -/
structure OriginalGeneratorMarkedSurface (g : ℕ) where
  carrier : Type
  topology : TopologicalSpace carrier
  surface : @ClosedRiemannSurface carrier topology
  genus : let := topology
    surface.HasGenus g
  point : carrier
  classes : let := topology
    Fin g × Fin 2 → FundamentalGroup carrier point
  canonical : let := topology
    IsOriginalCanonicalFamily surface g point classes

attribute [instance] OriginalGeneratorMarkedSurface.topology

namespace OriginalGeneratorMarkedSurface

variable {g : ℕ}

/-- One analytic homeomorphism and one common basepoint path identify every
ordered slot of the two original canonical families. -/
def Equivalent (M N : OriginalGeneratorMarkedSurface g) : Prop :=
  ∃ h : N.carrier ≃ₜ M.carrier,
    RiemannAnalyticMap N.surface.toRiemannAtlas M.surface.toRiemannAtlas h ∧
      ∃ c : Path (h N.point) M.point, ∀ i : Fin g × Fin 2,
        FundamentalGroup.fundamentalGroupMulEquivOfPath c
          (FundamentalGroup.map (⟨h, h.continuous⟩ : C(N.carrier, M.carrier))
            N.point (N.classes i)) = M.classes i

/-- The identity and constant path preserve the actual ordered family. -/
theorem equivalent_refl (M : OriginalGeneratorMarkedSurface g) : M.Equivalent M := by
  refine ⟨Homeomorph.refl _, RiemannAnalyticMap.id _, Path.refl M.point, ?_⟩
  intro i
  change FundamentalGroup.fundamentalGroupMulEquivOfPath (Path.refl M.point)
      (FundamentalGroup.map (ContinuousMap.id M.carrier) M.point (M.classes i)) = M.classes i
  simp only [FundamentalGroup.fundamentalGroupMulEquivOfPath_refl,
    FundamentalGroup.map_id]
  rfl

/-- The inverse analytic homeomorphism and reversed common path reverse the
same ordered-family identification. -/
theorem equivalent_symm {M N : OriginalGeneratorMarkedSurface g}
    (hMN : M.Equivalent N) : N.Equivalent M := by
  obtain ⟨h, hh, c, hc⟩ := hMN
  let f : C(N.carrier, M.carrier) := ⟨h, h.continuous⟩
  let k : C(M.carrier, N.carrier) := ⟨h.symm, h.symm.continuous⟩
  have hr : h.symm (h N.point) = N.point := h.symm_apply_apply N.point
  let d : Path (h.symm M.point) N.point :=
    (c.symm.map h.symm.continuous).cast rfl hr.symm
  have hcast {a b b' : N.carrier} (p : Path a b) (hb : b' = b)
      (x : FundamentalGroup N.carrier a) :
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.cast rfl hb) x =
        FundamentalGroup.mapOfEq (ContinuousMap.id N.carrier) hb.symm
          (FundamentalGroup.fundamentalGroupMulEquivOfPath p x) := by
    subst b'
    simp only [Path.cast_rfl_rfl]
    exact (TauCeti.FundamentalGroup.mapOfEq_id rfl
      (FundamentalGroup.fundamentalGroupMulEquivOfPath p x)).symm
  refine ⟨h.symm, riemannAnalyticMap_homeomorph_symm h hh, d, ?_⟩
  intro i
  change FundamentalGroup.fundamentalGroupMulEquivOfPath
      ((c.symm.map h.symm.continuous).cast rfl hr.symm)
      (FundamentalGroup.map k M.point (M.classes i)) = N.classes i
  rw [hcast, ← fundamentalGroup_map_basepoint_natural k c.symm]
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_symm, ← hc i,
    MulEquiv.symm_apply_apply]
  rw [← TauCeti.FundamentalGroup.mapOfEq_rfl (x := N.point) f,
    ← TauCeti.FundamentalGroup.mapOfEq_rfl (x := h N.point) k]
  calc
    _ = FundamentalGroup.mapOfEq k hr
        (FundamentalGroup.mapOfEq f rfl (N.classes i)) :=
      TauCeti.FundamentalGroup.mapOfEq_comp (ContinuousMap.id N.carrier) k rfl hr _
    _ = N.classes i :=
      TauCeti.FundamentalGroup.mapOfEq_mapOfEq_of_comp_eq_id k f rfl hr
        (ContinuousMap.ext fun x => h.symm_apply_apply x) (N.classes i)

/-- Composition uses the image of the second common path followed by the
first common path, without changing any ordered slot. -/
theorem equivalent_trans {M N P : OriginalGeneratorMarkedSurface g}
    (hMN : M.Equivalent N) (hNP : N.Equivalent P) : M.Equivalent P := by
  obtain ⟨h, hh, c, hc⟩ := hMN
  obtain ⟨k, hk, d, hd⟩ := hNP
  let f : C(N.carrier, M.carrier) := ⟨h, h.continuous⟩
  let v : C(P.carrier, N.carrier) := ⟨k, k.continuous⟩
  refine ⟨k.trans h, hh.comp hk, (d.map h.continuous).trans c, ?_⟩
  intro i
  change FundamentalGroup.fundamentalGroupMulEquivOfPath ((d.map h.continuous).trans c)
      (FundamentalGroup.map (f.comp v) P.point (P.classes i)) = M.classes i
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_trans, MulEquiv.trans_apply,
    FundamentalGroup.map_comp, MonoidHom.comp_apply]
  change FundamentalGroup.fundamentalGroupMulEquivOfPath c
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (d.map f.continuous)
        (FundamentalGroup.map f (k P.point)
          (FundamentalGroup.map v P.point (P.classes i)))) = M.classes i
  rw [← fundamentalGroup_map_basepoint_natural f d
    (FundamentalGroup.map v P.point (P.classes i)), hd i]
  exact hc i

/-- The literal analytic-homeomorphism and common-path equivalence relation. -/
def setoid (g : ℕ) : Setoid (OriginalGeneratorMarkedSurface g) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

end OriginalGeneratorMarkedSurface

/-- Original geometrically marked genus-g closed surfaces modulo analytic
homeomorphisms and simultaneous ordered basepoint transport. -/
def OriginalGeneratorTeichmullerSpace (g : ℕ) :=
  Quotient (OriginalGeneratorMarkedSurface.setoid g)

namespace OriginalGeneratorTeichmullerSpace

/-- The equivalence class of one actual geometrically marked surface. -/
def mk {g : ℕ} (M : OriginalGeneratorMarkedSurface g) : OriginalGeneratorTeichmullerSpace g :=
  Quotient.mk (OriginalGeneratorMarkedSurface.setoid g) M

end OriginalGeneratorTeichmullerSpace

end LowDimensionalTopology.Geometry.Teichmuller
