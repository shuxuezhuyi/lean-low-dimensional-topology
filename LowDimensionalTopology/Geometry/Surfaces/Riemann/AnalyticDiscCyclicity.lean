module

public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscCyclicGroups
public import LowDimensionalTopology.Geometry.Surfaces.Covering.DiscUniversalDeck
public import LowDimensionalTopology.Geometry.Surfaces.StandardAutomorphisms
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries

/-!
# Abelian free properly discontinuous analytic disc groups

For analytic automorphism groups, the hypotheses are the original free,
properly discontinuous analytic action and commutativity. Discreteness and
absence of elliptics are consequences. The conclusion includes the trivial
group. No quotient-space classification is part of this lemma.
-/

public section
noncomputable section

open Set
open scoped OnePoint UpperHalfPlane Manifold

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry
open DiscreteGroups DiscreteGroups.Action Hyperbolic Mobius

private theorem elliptic_fixed_in_geometric_disc
    {D : Set Mobius.ExtendedComplex} (hD : Mobius.IsComplexOpenDisc D)
    (f : Mobius.complexMobiusGroup) (hf : Mobius.MobiusElliptic f)
    (hp : f.val '' D = D) :
    ∃ z ∈ D, f.val z = z := by
  obtain ⟨q, hq⟩ := hD.normalize
  have hqi : q⁻¹.val '' extendedUnitDisc = D := by
    rw [← hq, Set.image_image]
    change (fun z => q⁻¹ • (q • z)) '' D = D
    simp only [inv_smul_smul, Set.image_id']
  have hpres : (q * f * q⁻¹).val '' extendedUnitDisc = extendedUnitDisc := by
    calc
      _ = q.val '' (f.val '' (q⁻¹.val '' extendedUnitDisc)) := by
        simp only [Set.image_image, Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_def]
      _ = extendedUnitDisc := by rw [hqi, hp, hq]
  have hE : Mobius.MobiusElliptic (q * f * q⁻¹) :=
    (Mobius.mobiusElliptic_conjugation f q).mpr hf
  obtain ⟨y, hy⟩ := mobiusElliptic_disc_fixed_inside _ hE hpres
  have hyin : y.val ∈ q.val '' D := by
    rw [hq]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hyin
  refine ⟨x, hx, ?_⟩
  apply (q : Equiv.Perm Mobius.ExtendedComplex).injective
  change q • (f • x) = q • x
  change q • (f • (q⁻¹ • y.val)) = y.val at hy
  have hxy' : q • x = y.val := hxy
  rw [← hxy', inv_smul_smul] at hy
  exact hy

/-- The exact free-action and compact-set discontinuity hypotheses imply the
native cyclicity theorem on every actual geometric disc or half-plane. -/
theorem abelian_free_discontinuous_geometric_disc_isCyclic
    (H : Subgroup Mobius.complexMobiusGroup)
    (D : Set Mobius.ExtendedComplex) (hD : Mobius.IsComplexOpenDisc D)
    (hp : ∀ g : H, g.val.val '' D = D)
    (hd : IsMobiusDiscontinuousOn H D)
    (hfree : ∀ g : H, ∀ z ∈ D, g.val.val z = z → g = 1)
    (hcomm : ∀ g h : H, Commute g h) : IsCyclic H := by
  have hInv : ∀ (g : H) z, z ∈ D → g • z ∈ D := by
    intro g z hz
    exact (hp g).subset (Set.mem_image_of_mem _ hz)
  have hne : D.Nonempty := by
    obtain ⟨S, _hS, z, hz, rfl⟩ := hD
    exact ⟨z, mem_connectedComponentIn hz⟩
  have hdiscrete := isMobiusDiscontinuousOn_invariant_discrete H D hInv hne hd
  have hno : ∀ f ∈ H, ¬Mobius.MobiusElliptic f := by
    intro f hf hE
    obtain ⟨z, hz, hfix⟩ := elliptic_fixed_in_geometric_disc hD f hE (hp ⟨f, hf⟩)
    exact hE.1 (congrArg Subtype.val (hfree ⟨f, hf⟩ z hz hfix))
  exact discrete_abelian_noElliptic_invariantDisc_isCyclic H hdiscrete
    ⟨D, hD, hp⟩ hcomm hno

private theorem cyclic_of_faithful_mobius_model
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (F : G →* Mobius.complexMobiusGroup) (hi : Function.Injective F)
    (D : Set Mobius.ExtendedComplex) (hD : Mobius.IsComplexOpenDisc D)
    (hp : ∀ g, (F g).val '' D = D) (e : X ≃ₜ D)
    (he : ∀ (g : G) (x : X), (e (g • x)).val = (F g).val (e x).val)
    (hd : IsDiscontinuous G X)
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1)
    (hcomm : ∀ (g h : G), Commute g h) : IsCyclic G := by
  let H := F.range
  have hpres (g : H) : g.val.val '' D = D := by
    obtain ⟨a, ha⟩ := g.property
    rw [← ha]
    exact hp a
  have hInv : ∀ (g : H) z, z ∈ D → g • z ∈ D := by
    intro g z hz
    exact (hpres g).subset (Set.mem_image_of_mem _ hz)
  let : MulAction H D := invariantSubsetMulAction D hInv
  let φ := F.ofInjective hi
  have heq (g : G) (x : X) : e (g • x) = φ g • e x := by
    apply Subtype.ext
    exact he g x
  have hdisc : IsMobiusDiscontinuousOn H D :=
    (isMobiusDiscontinuousOn_iff_subtype H D hInv).mpr
      (hd.transport φ.toEquiv e heq)
  have hfreeH (g : H) (z : Mobius.ExtendedComplex) (hz : z ∈ D)
      (hfix : g.val.val z = z) : g = 1 := by
    obtain ⟨a, ha⟩ := g.property
    have hax : a • e.symm ⟨z, hz⟩ = e.symm ⟨z, hz⟩ := by
      apply e.injective
      apply Subtype.ext
      rw [he, e.apply_symm_apply, ha]
      exact hfix
    apply Subtype.ext
    rw [← ha, hfree a _ hax, map_one, Subgroup.coe_one]
  have hcommH (g h : H) : Commute g h := by
    obtain ⟨a, ha⟩ := g.property
    obtain ⟨b, hb⟩ := h.property
    apply Subtype.ext
    change g.val * h.val = h.val * g.val
    rw [← ha, ← hb, ← map_mul, ← map_mul, (hcomm a b).eq]
  let : IsCyclic H := abelian_free_discontinuous_geometric_disc_isCyclic
    H D hD hpres hdisc hfreeH hcommH
  exact isCyclic_of_injective φ.toMonoidHom φ.injective

/-- An arbitrary actual analytic subgroup of disc homeomorphisms satisfying
the original free, properly discontinuous and abelian hypotheses is cyclic. -/
theorem abelian_free_discontinuous_analytic_disc_isCyclic
    (K : Subgroup (extendedUnitDisc ≃ₜ extendedUnitDisc))
    (ha : ∀ g : K, RiemannAnalyticMap discRiemannSurface.toRiemannAtlas
      discRiemannSurface.toRiemannAtlas g.val)
    (hd : IsDiscontinuous K extendedUnitDisc)
    (hfree : ∀ g : K, ∀ z : extendedUnitDisc, g • z = z → g = 1)
    (hcomm : ∀ g h : K, Commute g h) : IsCyclic K := by
  exact cyclic_of_faithful_mobius_model
    (discAnalyticActionMobiusHom K.subtype ha)
    (discAnalyticActionMobiusHom_injective K.subtype ha Subtype.val_injective)
    extendedUnitDisc extendedUnitDisc_isComplexOpenDisc
    (fun g => discAnalyticAutomorphismMobius_preserves g.val (ha g))
    (Homeomorph.refl extendedUnitDisc)
    (fun g z => (discAnalyticAutomorphismMobius_apply g.val (ha g) z).symm)
    hd hfree hcomm

/-- Every free properly discontinuous abelian analytic half-plane group is cyclic.
The original holomorphic homeomorphisms determine their unique global Mobius
maps; no matrix representation, discreteness or absence of elliptics is assumed. -/
theorem abelian_free_discontinuous_analytic_halfPlane_isCyclic
    (K : Subgroup (ℍ ≃ₜ ℍ))
    (ha : ∀ g : K, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g.val)
    (hd : IsDiscontinuous K ℍ)
    (hfree : ∀ g : K, ∀ z : ℍ, g • z = z → g = 1)
    (hcomm : ∀ g h : K, Commute g h) : IsCyclic K := by
  choose A hA using fun g : K => LiZhongQC.k22c5_eq_smul_of_mdifferentiable g.val (ha g)
  have hF (g : K) (z : ℍ) :
      (realSLMobius (A g)).val (z : ℂ) = (((g • z : ℍ) : ℂ) : Mobius.ExtendedComplex) := by
    calc
      _ = (((A g • z : ℍ) : ℂ) : Mobius.ExtendedComplex) := realSLMobius_action (A g) z
      _ = _ := congrArg (fun w : ℍ => ((w : ℂ) : Mobius.ExtendedComplex)) (hA g z).symm
  let F : K →* Mobius.complexMobiusGroup :=
    { toFun := fun g => realSLMobius (A g)
      map_one' := by
        apply Fuchsian.mobius_ext_on_halfPlane
        intro z
        exact (hF 1 z).trans (by rfl)
      map_mul' := by
        intro g h
        apply Fuchsian.mobius_ext_on_halfPlane
        intro z
        change (realSLMobius (A (g * h))).val (z : ℂ) =
          (realSLMobius (A g)).val ((realSLMobius (A h)).val (z : ℂ))
        calc
          _ = ((((g * h) • z : ℍ) : ℂ) : Mobius.ExtendedComplex) := hF (g * h) z
          _ = (((g • (h • z) : ℍ) : ℂ) : Mobius.ExtendedComplex) := rfl
          _ = (realSLMobius (A g)).val (((h • z : ℍ) : ℂ) : Mobius.ExtendedComplex) :=
            (hF g (h • z)).symm
          _ = _ := congrArg (realSLMobius (A g)).val (hF h z).symm }
  have hi : Function.Injective F := by
    intro g h hgh
    apply Subtype.ext
    apply Homeomorph.ext
    intro z
    apply UpperHalfPlane.ext
    have hv := congrArg (fun M : Mobius.complexMobiusGroup => M.val (z : ℂ)) hgh
    change (realSLMobius (A g)).val (z : ℂ) =
      (realSLMobius (A h)).val (z : ℂ) at hv
    rw [hF, hF] at hv
    exact OnePoint.coe_injective hv
  refine cyclic_of_faithful_mobius_model F hi openHalfPlaneSet
    openHalfPlaneSet_isComplexOpenDisc
    (fun g => Fuchsian.realSLMobius_image_openHalfPlane (A g))
    halfPlaneOpenModelHomeomorph ?_ hd hfree hcomm
  intro g z
  change (((g • z : ℍ) : ℂ) : Mobius.ExtendedComplex) =
    (realSLMobius (A g)).val (z : ℂ)
  exact (hF g z).symm

end LowDimensionalTopology.Geometry.Surfaces
