module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleWindings
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
namespace LowDimensionalTopology.Geometry.Surfaces

theorem riemannSphere_not_homeomorphic_torus :
    ¬Nonempty ((OnePoint ℂ)≃ₜ(AddCircle (1:ℝ)×AddCircle (1:ℝ))) := by
  rintro ⟨e⟩
  let _:=riemannSphere_simplyConnected
  let _:SimplyConnectedSpace (AddCircle (1:ℝ)×AddCircle (1:ℝ)):=
    e.symm.toHomotopyEquiv.simplyConnectedSpace
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.torusProductFundamentalGroup_not_isCyclic 0 inferInstance

/-- A genuine sphere genus witness determines the genus of every handle-model witness. -/
theorem hasTopologicalGenus_zero_unique {X:Type*} [TopologicalSpace X] {g:ℕ}
    (h0:HasTopologicalGenus X 0) (hg:HasTopologicalGenus X g) : g=0 := by
  obtain ⟨e0⟩:=(hasTopologicalGenus_zero_iff).mp h0
  let E:OnePoint ℂ≃ₜMetric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1:=
    onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
  let f:X≃ₜOnePoint ℂ:=e0.trans E.symm
  by_cases h:g=0
  · exact h
  by_cases h1:g=1
  · obtain ⟨e1⟩:=hasTopologicalGenus_one_iff.mp (h1 ▸hg)
    exact False.elim (riemannSphere_not_homeomorphic_torus ⟨f.symm.trans e1⟩)
  exact False.elim ((hasTopologicalGenus_ge_two_not_sphere_not_torus (by omega) hg).1 ⟨f⟩)

/-- A genuine torus genus witness likewise determines every other handle-model witness. -/
theorem hasTopologicalGenus_one_unique {X:Type*} [TopologicalSpace X] {g:ℕ}
    (h1:HasTopologicalGenus X 1) (hg:HasTopologicalGenus X g) : g=1 := by
  obtain ⟨e1⟩:=hasTopologicalGenus_one_iff.mp h1
  by_cases h:g=1
  · exact h
  by_cases h0:g=0
  · have he: (1:ℕ)=0:=hasTopologicalGenus_zero_unique (h0 ▸hg) h1
    omega
  exact False.elim ((hasTopologicalGenus_ge_two_not_sphere_not_torus (by omega) hg).2 ⟨e1⟩)

theorem hasTopologicalGenus_unique_of_le_one {X:Type*} [TopologicalSpace X] {g h:ℕ}
    (hg:HasTopologicalGenus X g) (hh:HasTopologicalGenus X h) (hle:g≤1) : g=h := by
  rcases (show g=0∨g=1 by omega) with rfl|rfl
  · exact (hasTopologicalGenus_zero_unique hg hh).symm
  · exact (hasTopologicalGenus_one_unique hg hh).symm

end LowDimensionalTopology.Geometry.Surfaces
