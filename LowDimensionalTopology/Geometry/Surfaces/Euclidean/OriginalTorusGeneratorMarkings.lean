module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.GeneratorLoopTransport
public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.TorusMarkedHomotopy
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CompactGenusTypes

/-!
# Actual generator-marked original tori

All surfaces, maps, loop classes, and basepoints are the original ones.
Uniformization supplies genuine plane-cover torus models internally. The
source cover is translated so its distinguished point lies over the given
original basepoint; this does not change the surface or its complex atlas.

The final theorem needs only that the two original loop classes generate
the actual fundamental group. Every canonical torus system has that property.
No geometric realization of arbitrary higher-genus class tuples is asserted.
-/

@[expose] public section
noncomputable section

open Set Module

namespace LowDimensionalTopology.Geometry.Surfaces

namespace ComplexTorusModel

/-- Translate the genuine plane cover, preserving the original surface atlas
and the entire original period lattice. -/
def recenter {b : Basis (Fin 2) ℝ ℂ} (T : ComplexTorusModel b) (a : ℂ) : ComplexTorusModel b where
  surface := T.surface
  projection z := T.projection (z + a)
  covering := T.covering.comp_homeomorph (Homeomorph.addRight a)
  surjective := T.surjective.comp (Homeomorph.addRight a).surjective
  analytic_projection := by
    apply T.analytic_projection.comp
    apply (RiemannAnalyticMap.globalChart_iff (OpenPartialHomeomorph.refl ℂ) rfl
      (OpenPartialHomeomorph.refl ℂ) rfl (fun z => z + a)).mpr
    refine ⟨continuous_id.add continuous_const, ?_⟩
    change AnalyticOnNhd ℂ (fun z => z + a) _
    intro z _hz
    exact analyticAt_id.add analyticAt_const
  fiber_iff := by
    intro z w
    have he : (z + a) - (w + a) = z - w := by abel
    simpa only [he] using T.fiber_iff (z + a) (w + a)

end ComplexTorusModel

private theorem exists_torus_model_of_topologicalGenus_one
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X)
    (hR : HasTopologicalGenus X 1) :
    ∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b,
      RiemannConformallyEquivalent R T.surface := by
  let : CompactSpace X := HandleSeparation.hasTopologicalGenus_compactSpace hR
  obtain ⟨e⟩ := hasTopologicalGenus_one_iff.mp hR
  obtain ⟨C⟩ := riemannSurface_nonempty_universalCover R
  exact C.compact_plane_model_torus (C.plane_model_of_homeomorphic_torus e)

/-- On arbitrary original tori, the genuine homotopy class of any two
continuous maps is determined by their actual original generating loop
classes and ONE common basepoint-transport path. -/
theorem RiemannSurface.torus_homotopic_iff_generator_transport
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (R : RiemannSurface X) (S : RiemannSurface Y)
    (hR : HasTopologicalGenus X 1) (hS : HasTopologicalGenus Y 1)
    (f g : C(X, Y)) (x : X) (sigma : Fin 2 → FundamentalGroup X x)
    (hgen : Subgroup.closure (Set.range sigma) = ⊤) :
    ContinuousMap.Homotopic f g ↔ GeneratorMapsTransported f g x sigma := by
  constructor
  · exact fun h => GeneratorMapsTransported.of_homotopic h x sigma
  · intro h
    obtain ⟨C, hC⟩ := GeneratorMapsTransported.all hgen h
    obtain ⟨b, T, e, he, hbij⟩ := exists_torus_model_of_topologicalGenus_one R hR
    obtain ⟨c, U, v, hv, hvbij⟩ := exists_torus_model_of_topologicalGenus_one S hS
    let E := he.toHomeomorph hbij
    let V := hv.toHomeomorph hvbij
    obtain ⟨a, ha⟩ := T.surjective (E x)
    let T₀ := T.recenter a
    have hzero : T₀.projection 0 = E x := by
      change T.projection (0 + a) = E x
      simpa only [zero_add] using ha
    let u : C(ComplexTorusCarrier, X) := ⟨E.symm, E.symm.continuous⟩
    let w : C(Y, ComplexTorusCarrier) := ⟨V, V.continuous⟩
    let F := w.comp (f.comp u)
    let G := w.comp (g.comp u)
    obtain ⟨D, hD⟩ := basedLoop_transport_precompose C hC u (T₀.projection 0)
      (by change E.symm (T₀.projection 0) = x; rw [hzero, E.symm_apply_apply])
    have hW := basedLoop_transport_postcompose D hD w
    have hloops : ∀ i : Fin 2, Path.Homotopic
        (((T₀.periodLoop (b i) (Submodule.subset_span (Set.mem_range_self i))).map
          F.continuous).trans (D.map w.continuous))
        ((D.map w.continuous).trans ((T₀.periodLoop (b i)
          (Submodule.subset_span (Set.mem_range_self i))).map G.continuous)) := by
      intro i
      exact (basedLoop_transport_iff F G (T₀.projection 0) (D.map w.continuous)
        (T₀.periodLoop (b i) (Submodule.subset_span (Set.mem_range_self i)))).mp
          (hW (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (T₀.periodLoop (b i) (Submodule.subset_span (Set.mem_range_self i))))))
    have hFG : ContinuousMap.Homotopic F G :=
      (T₀.homotopic_iff_transported_basis_loops U F G).mpr ⟨D.map w.continuous, hloops⟩
    let V' : C(ComplexTorusCarrier, Y) := ⟨V.symm, V.symm.continuous⟩
    let E' : C(X, ComplexTorusCarrier) := ⟨E, E.continuous⟩
    have hback := ((ContinuousMap.Homotopic.refl V').comp hFG).comp
      (ContinuousMap.Homotopic.refl E')
    have hf : (V'.comp F).comp E' = f := by
      ext z
      simp only [ContinuousMap.comp_apply, F, V', E', w, u, ContinuousMap.coe_mk,
        E.symm_apply_apply, V.symm_apply_apply]
    have hg : (V'.comp G).comp E' = g := by
      ext z
      simp only [ContinuousMap.comp_apply, G, V', E', w, u, ContinuousMap.coe_mk,
        E.symm_apply_apply, V.symm_apply_apply]
    rw [hf, hg] at hback
    exact hback

/-- Biholomorphic equivalence of the two actual pushed-forward generator
markings. The target basepoints may differ and one actual path transports
both original generator classes simultaneously. -/
def GeneratorMarkedTargetsEquivalent
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (S : RiemannSurface Y) (S' : RiemannSurface Z)
    (f : X ≃ₜ Y) (g : X ≃ₜ Z) (x : X) (sigma : Fin 2 → FundamentalGroup X x) : Prop :=
  ∃ h : Y ≃ₜ Z, RiemannAnalyticMap S.toRiemannAtlas S'.toRiemannAtlas h ∧
    GeneratorMapsTransported
      ((⟨h, h.continuous⟩ : C(Y, Z)).comp ⟨f, f.continuous⟩) ⟨g, g.continuous⟩ x sigma

/-- The original genus-one generator-marked target relation agrees exactly
with homotopy of `g` after `f` inverse to SOME biholomorphism.
Both biholomorphism witnesses are existential; none is assumed as input.
The statement applies in particular to the book's oriented diffeomorphisms. -/
theorem ClosedRiemannSurface.torus_generator_marked_targets_iff_homotopic_biholomorph
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (R : ClosedRiemannSurface X) (hR : R.HasGenus 1)
    (S : RiemannSurface Y) (S' : RiemannSurface Z)
    (f : X ≃ₜ Y) (g : X ≃ₜ Z) (x : X) (sigma : Fin 2 → FundamentalGroup X x)
    (hgen : Subgroup.closure (Set.range sigma) = ⊤) :
    GeneratorMarkedTargetsEquivalent S S' f g x sigma ↔
      ∃ h : Y ≃ₜ Z, RiemannAnalyticMap S.toRiemannAtlas S'.toRiemannAtlas h ∧
        ContinuousMap.Homotopic
          ((⟨g, g.continuous⟩ : C(X, Z)).comp ⟨f.symm, f.symm.continuous⟩)
          ⟨h, h.continuous⟩ := by
  let fm : C(X, Y) := ⟨f, f.continuous⟩
  let fi : C(Y, X) := ⟨f.symm, f.symm.continuous⟩
  let gm : C(X, Z) := ⟨g, g.continuous⟩
  constructor
  · rintro ⟨h, hh, hmark⟩
    have hZ : HasTopologicalGenus Z 1 := by
      obtain ⟨er⟩ := hR
      exact ⟨g.symm.trans er⟩
    let hm : C(Y, Z) := ⟨h, h.continuous⟩
    have hmaps : ContinuousMap.Homotopic (hm.comp fm) gm :=
      (R.toRiemannSurface.torus_homotopic_iff_generator_transport S' hR hZ
        (hm.comp fm) gm x sigma hgen).mpr hmark
    have hpre := hmaps.comp (ContinuousMap.Homotopic.refl fi)
    have he : (hm.comp fm).comp fi = hm := by
      ext z
      simp only [ContinuousMap.comp_apply, hm, fm, fi, ContinuousMap.coe_mk,
        f.apply_symm_apply]
    rw [he] at hpre
    exact ⟨h, hh, hpre.symm⟩
  · rintro ⟨h, hh, hhom⟩
    let hm : C(Y, Z) := ⟨h, h.continuous⟩
    have hpost := hhom.comp (ContinuousMap.Homotopic.refl fm)
    have he : (gm.comp fi).comp fm = gm := by
      ext z
      simp only [ContinuousMap.comp_apply, gm, fi, fm, ContinuousMap.coe_mk,
        f.symm_apply_apply]
    rw [he] at hpost
    exact ⟨h, hh, GeneratorMapsTransported.of_homotopic hpost.symm x sigma⟩

end LowDimensionalTopology.Geometry.Surfaces
