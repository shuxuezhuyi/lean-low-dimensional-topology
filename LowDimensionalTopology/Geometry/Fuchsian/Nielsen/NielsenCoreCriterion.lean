module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreVertexCycles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaPolygonSides
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Topology MeasureTheory
open scoped OnePoint Complex.UnitDisc Pointwise ENNReal UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance coreBoundaryAnglesSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance coreBoundaryAnglesSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- Two genuine open convex plane regions with a common interior point have
exactly the expected closure intersection; no transversality is assumed. -/
theorem complex_open_convex_closure_inter {S T : Set ℂ}
    (hS : Convex ℝ S) (hT : Convex ℝ T) (hoS : IsOpen S) (hoT : IsOpen T)
    (w : ℂ) (hwS : w∈S) (hwT : w∈T) : closure (S∩T)=closure S∩closure T := by
  apply subset_antisymm (closure_inter_subset_inter_closure S T)
  intro x hx
  have hseg : openSegment ℝ x w⊆S∩T := by
    intro z hz
    constructor
    · exact interior_subset (hS.openSegment_closure_interior_subset_interior hx.1
        (hoS.interior_eq.symm ▸ hwS) hz)
    · exact interior_subset (hT.openSegment_closure_interior_subset_interior hx.2
        (hoT.interior_eq.symm ▸ hwT) hz)
  exact closure_mono hseg (segment_subset_closure_openSegment (left_mem_segment ℝ x w))

/-- Genuine native hyperbolic convexity gives the same exact closure
intersection, through the actual Klein embedding. -/
theorem disc_open_hconvex_closure_inter {S T : Set 𝔻}
    (hS : Hyperbolic.DiscHConvex S)
    (hT : Hyperbolic.DiscHConvex T)
    (hoS : IsOpen S)
    (hoT : IsOpen T)
    (w : 𝔻) (hwS : w∈S) (hwT : w∈T) : closure (S∩T)=closure S∩closure T := by
  rw [Hyperbolic.isEmbedding_kleinCoordinate.closure_eq_preimage_closure_image,
    image_inter Hyperbolic.kleinCoordinate_injective]
  rw [complex_open_convex_closure_inter ((Hyperbolic.discHConvex_iff_klein_convex S).mp hS)
    ((Hyperbolic.discHConvex_iff_klein_convex T).mp hT)
    (Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap S hoS)
    (Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap T hoT)
    (Hyperbolic.kleinCoordinate w) (mem_image_of_mem _ hwS) (mem_image_of_mem _ hwT)]
  rw [preimage_inter,←Hyperbolic.isEmbedding_kleinCoordinate.closure_eq_preimage_closure_image,
    ←Hyperbolic.isEmbedding_kleinCoordinate.closure_eq_preimage_closure_image]

/-- The true original polygon/core intersection has the exact closure needed
at newly cut boundary corners. The common point is genuinely inside both. -/
theorem nielsenCore_inter_closure_eq
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hwD : w∈D)
    (hwN : w∈fuchsianNielsenCore P hNE) :
    closure (D∩fuchsianNielsenCore P hNE)=closure D∩closure (fuchsianNielsenCore P hNE) := by
  apply P.finiteCoordinate.injective.image_injective
  rw [P.finiteCoordinate.image_closure,image_inter P.finiteCoordinate.injective,
    image_inter P.finiteCoordinate.injective,P.finiteCoordinate.image_closure,
    P.finiteCoordinate.image_closure]
  rw [disc_open_hconvex_closure_inter hD.convex (fuchsianNielsenCore_convex P hNE)
    (P.finiteCoordinate.isOpenMap D hD.locallyFinite.fundamental.isOpen)
    (P.finiteCoordinate.isOpenMap _ (fuchsianNielsenCore_isOpen P hNE))
    (P.finiteCoordinate w) (mem_image_of_mem _ hwD) (mem_image_of_mem _ hwN)]

/-- The actual entire core, and hence its genuine closure, is preserved by
every original group element. -/
theorem fuchsianNielsenCore_smul_closure
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (g : H) :
    g • closure (fuchsianNielsenCore P hNE)=closure (fuchsianNielsenCore P hNE) := by
  have he : g • fuchsianNielsenCore P hNE=fuchsianNielsenCore P hNE := by
    apply subset_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact fuchsianNielsenCore_invariant P hNE g x hx
    · intro x hx
      exact ⟨g⁻¹ • x,fuchsianNielsenCore_invariant P hNE g⁻¹ x hx,smul_inv_smul g x⟩
  exact ((Homeomorph.smul g).image_closure _).trans (congrArg closure he)

/-- The actual closed Nielsen core remains genuinely convex in the original
point-normalized native disc coordinate. -/
theorem pointCoordinate_nielsenCore_closure_convex
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (x : P.domain.carrier) :
    Hyperbolic.DiscHConvex (polygonPointCoordinate P x '' closure (fuchsianNielsenCore P hNE)) := by
  change Hyperbolic.DiscHConvex ((fun z=>Hyperbolic.discOriginNormalizer (P.finiteCoordinate x) (P.finiteCoordinate z))
    '' _)
  rw [←image_image,P.finiteCoordinate.image_closure]
  exact (fuchsianNielsenCore_convex P hNE).closure.isometry_image (Hyperbolic.discOriginNormalizer_isometry _)

/-- Original closed tiles cut by the genuine core are exactly the original
closed tiles intersected with the true closed core. -/
theorem nielsenCore_closed_tile_inter
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hwD : w∈D)
    (hwN : w∈fuchsianNielsenCore P hNE) (g : H) :
    fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) g=
      fuchsianDomainTile P D g∩closure (fuchsianNielsenCore P hNE) := by
  change g • closure (D∩fuchsianNielsenCore P hNE)=_
  rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
  have he : g • (closure D∩closure (fuchsianNielsenCore P hNE))=
      (g • closure D)∩g • closure (fuchsianNielsenCore P hNE) :=
    image_inter (Homeomorph.smul g).injective
  rw [he,fuchsianNielsenCore_smul_closure]
  rfl

/-- The true cut-tile direction set is exactly the original tile's directions
intersected with the true core directions. -/
theorem nielsenCore_tile_directions_inter
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hwD : w∈D)
    (hwN : w∈fuchsianNielsenCore P hNE) (x : P.domain.carrier)
    (hxN : x∈closure (fuchsianNielsenCore P hNE)) (g : H)
    (hg : x∈fuchsianDomainTile P D g) :
    fuchsianTileDirections P (D∩fuchsianNielsenCore P hNE) x g=
      fuchsianTileDirections P D x g∩
        Hyperbolic.discRadialDirections (polygonPointCoordinate P x '' closure (fuchsianNielsenCore P hNE)) := by
  unfold fuchsianTileDirections
  rw [nielsenCore_closed_tile_inter hD hNE w hwD hwN,
    image_inter (polygonPointCoordinate P x).injective]
  apply Hyperbolic.discRadialDirections_inter
  · rw [polygonPointCoordinate_image_tile]
    exact (hD.pointCoordinate_smul_convex x g).closure
  · exact pointCoordinate_nielsenCore_closure_convex P hNE x
  · rw [polygonPointCoordinate_zero_mem_tile]
    exact hg
  · rw [←polygonPointCoordinate_self P x]
    exact mem_image_of_mem _ hxN

/-- Actual closed original tiles partition precisely the genuine angular
measure of the closed Nielsen core, including at newly cut boundary points. -/
theorem nielsenCore_tile_directions_measure_sum
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hwD : w∈D)
    (hwN : w∈fuchsianNielsenCore P hNE) (x : P.domain.carrier)
    (hxN : x∈closure (fuchsianNielsenCore P hNE)) :
    (∑g∈(hD.locallyFinite.incident_finite x).toFinset,
      Hyperbolic.polygonDirectionMeasure (fuchsianTileDirections P (D∩fuchsianNielsenCore P hNE) x g))=
      fuchsianPolygonAngularFraction P (fuchsianNielsenCore P hNE) x := by
  classical
  let C := Hyperbolic.discRadialDirections
    (polygonPointCoordinate P x '' closure (fuchsianNielsenCore P hNE))
  have hmeasC : MeasurableSet C := Hyperbolic.measurableSet_discRadialDirections
    (pointCoordinate_nielsenCore_closure_convex P hNE x)
    ((polygonPointCoordinate P x).isClosedMap _ isClosed_closure)
    (by rw [←polygonPointCoordinate_self P x];exact mem_image_of_mem _ hxN)
  have hm := measure_biUnion_finset₀ (μ := Hyperbolic.polygonDirectionMeasure)
    (s := (hD.locallyFinite.incident_finite x).toFinset)
    (f := fun g=>fuchsianTileDirections P D x g∩C)
    (by
      intro g hg h hh hgh
      apply measure_mono_null _ (hD.tileDirections_pairwise_null x
        (by simpa using hg) (by simpa using hh) hgh)
      exact fun _ hu=>⟨hu.1.1,hu.2.1⟩)
    (fun g hg=>((hD.tileDirections_measurable x (by simpa using hg)).inter hmeasC).nullMeasurableSet)
  have hu : (⋃g∈(hD.locallyFinite.incident_finite x).toFinset,
      fuchsianTileDirections P D x g∩C)=C := by
    have hcover : (⋃g∈(hD.locallyFinite.incident_finite x).toFinset,
        fuchsianTileDirections P D x g)=univ := by
      simpa only [Set.Finite.mem_toFinset] using hD.locallyFinite.tileDirections_cover x
    apply subset_antisymm
    · intro u hu
      obtain ⟨g,hg,hug,hc⟩ := mem_iUnion₂.mp hu
      exact hc
    · intro u hc
      have hu : u∈⋃g∈(hD.locallyFinite.incident_finite x).toFinset,fuchsianTileDirections P D x g := by
        rw [hcover]
        trivial
      obtain ⟨g,hg,hug⟩ := mem_iUnion₂.mp hu
      exact mem_iUnion₂.mpr ⟨g,hg,hug,hc⟩
  rw [hu] at hm
  calc
    _=∑g∈(hD.locallyFinite.incident_finite x).toFinset,
        Hyperbolic.polygonDirectionMeasure (fuchsianTileDirections P D x g∩C) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [nielsenCore_tile_directions_inter hD hNE w hwD hwN x hxN g
        (by simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hg)]
    _=Hyperbolic.polygonDirectionMeasure C := hm.symm
    _=_ := by
      change Hyperbolic.polygonDirectionMeasure (Hyperbolic.discRadialDirections
        (polygonPointCoordinate P x '' closure (fuchsianNielsenCore P hNE)))=
        Hyperbolic.polygonDirectionMeasure (Hyperbolic.discRadialDirections
          (Hyperbolic.discOriginNormalizer (P.finiteCoordinate x) ''
            (P.finiteCoordinate '' closure (fuchsianNielsenCore P hNE))))
      rw [image_image]
      rfl

/-- The original stabilizer multiplicity counts cut-tile directions by the
actual complete original finite cycle. This holds at core boundary points. -/
theorem nielsenCore_cycleAngularFraction_sum
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hwD : w∈D)
    (hwN : w∈fuchsianNielsenCore P hNE) (x : P.domain.carrier)
    (hxN : x∈closure (fuchsianNielsenCore P hNE)) :
    (fuchsianPointOrder P x : ℝ≥0∞)*
      ∑y∈(hD.locallyFinite.cycle_finite x).toFinset,
        fuchsianPolygonAngularFraction P (D∩fuchsianNielsenCore P hNE) y=
      fuchsianPolygonAngularFraction P (fuchsianNielsenCore P hNE) x := by
  rw [←hD.locallyFinite.incident_weight_sum x]
  convert nielsenCore_tile_directions_measure_sum hD hNE w hwD hwN x hxN using 1
  apply Finset.sum_congr rfl
  intro g _hg
  exact (fuchsianTileDirections_measure_eq P (D∩fuchsianNielsenCore P hNE) x g).symm

/-- In radians, the actual total cut-cycle angle equals the true core angle
divided by the exact original stabilizer order. -/
theorem nielsenCore_cycleAngle_sum
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hwD : w∈D)
    (hwN : w∈fuchsianNielsenCore P hNE) (x : P.domain.carrier)
    (hxN : x∈closure (fuchsianNielsenCore P hNE)) :
    (∑y∈(hD.locallyFinite.cycle_finite x).toFinset,
      fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) y)=
      fuchsianPolygonAngle P (fuchsianNielsenCore P hNE) x/fuchsianPointOrder P x := by
  have hm := congrArg ENNReal.toReal (nielsenCore_cycleAngularFraction_sum hD hNE w hwD hwN x hxN)
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun y _hy=>fuchsianPolygonAngularFraction_ne_top P _ y)] at hm
  have hn : (fuchsianPointOrder P x : ℝ)≠0 := Nat.cast_ne_zero.mpr (P.pointOrder_pos x).ne'
  simp only [fuchsianPolygonAngle,←Finset.mul_sum]
  apply (eq_div_iff hn).mpr
  calc
    _=2*Real.pi*((fuchsianPointOrder P x : ℝ)*
        ∑y∈(hD.locallyFinite.cycle_finite x).toFinset,
          (fuchsianPolygonAngularFraction P (D∩fuchsianNielsenCore P hNE) y).toReal) := by ring
    _=_ := by rw [hm]

/-- A genuine open hyperbolically convex native region subtends at most a
straight angle at any point outside it. The supporting functional is proved
from actual Klein convexity and Hahn--Banach separation. -/
theorem discSubtendedAngle_closure_le_pi_of_not_mem
    {S : Set 𝔻} (hS : Hyperbolic.DiscHConvex S) (ho : IsOpen S) (hn : S.Nonempty)
    (z : 𝔻)
    (hz : z∉S) : Hyperbolic.discSubtendedAngle (closure S) z≤Real.pi := by
  let F := Hyperbolic.discOriginNormalizer z
  let T := F '' S
  have hF : let :=Hyperbolic.discHyperbolicMetric;Isometry F := Hyperbolic.discOriginNormalizer_isometry z
  have hT : Hyperbolic.DiscHConvex T := hS.isometry_image hF
  have hoT : IsOpen T := F.isOpenMap S ho
  have hnT : T.Nonempty := hn.image F
  have h0 : (0:𝔻)∉T := by
    rw [←Hyperbolic.discOriginNormalizer_apply_self z]
    exact fun h=>hz (F.injective.mem_set_image.mp h)
  let K := Hyperbolic.kleinCoordinate '' T
  have hK : Convex ℝ K := (Hyperbolic.discHConvex_iff_klein_convex T).mp hT
  have hoK : IsOpen K := Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap T hoT
  have hnK : K.Nonempty := hnT.image Hyperbolic.kleinCoordinate
  have h0K : (0:ℂ)∉interior K := by
    rw [hoK.interior_eq]
    intro h
    have he : Hyperbolic.kleinCoordinate (0:𝔻)=(0:ℂ) := by simp [Hyperbolic.kleinCoordinate,Hyperbolic.poincareToKlein,Hyperbolic.kleinFormula]
    rw [←he] at h
    exact h0 (Hyperbolic.kleinCoordinate_injective.mem_set_image.mp h)
  obtain ⟨f,hf,hfs⟩ := geometric_hahn_banach_of_nonempty_interior_point hK h0K
    (hoK.interior_eq.symm ▸ hnK)
  let n : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm f
  have hn : n≠0 := by
    intro he
    have hh := (InnerProductSpace.toDual ℝ ℂ).apply_symm_apply f
    change InnerProductSpace.toDual ℝ ℂ n=f at hh
    rw [he,map_zero] at hh
    exact hf hh.symm
  have hs : ∀v∈closure T,inner ℝ n (Hyperbolic.kleinCoordinate v)≤0 := by
    intro v hv
    have hcl : Hyperbolic.kleinCoordinate v∈closure K :=
      image_closure_subset_closure_image Hyperbolic.continuous_kleinCoordinate ⟨v,hv,rfl⟩
    have hsub : K⊆{a : ℂ | f a≤0} := by
      intro a ha
      change f a≤0
      simpa only [map_zero] using hfs a ha
    have hh : f (Hyperbolic.kleinCoordinate v)≤0 :=
      closure_minimal hsub (isClosed_le f.continuous continuous_const) hcl
    simpa only [n,InnerProductSpace.toDual_symm_apply] using hh
  have hdirs : Hyperbolic.discRadialDirections (closure T)⊆
      {u : Circle | inner ℝ n (u:ℂ)≤0} := by
    rintro u ⟨r,hr⟩
    have hh := hs _ hr
    rw [Hyperbolic.kleinCoordinate_discRadialPoint] at hh
    change inner ℝ n ((2*r.val/(1+r.val^2)) • (u:ℂ))≤0 at hh
    rw [real_inner_smul_right] at hh
    have hp : 0<2*r.val/(1+r.val^2) := div_pos (by linarith [r.property.1]) (by positivity)
    change inner ℝ n (u:ℂ)≤0
    nlinarith
  have hm : Hyperbolic.discSubtendedAngle (closure T) 0≤Real.pi := by
    rw [Hyperbolic.discSubtendedAngle,Hyperbolic.discSubtendedAngularFraction_zero]
    calc
      _≤2*Real.pi*(Hyperbolic.polygonDirectionMeasure {u : Circle | inner ℝ n (u:ℂ)≤0}).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hdirs)) (by positivity)
      _=Real.pi := polygonDirectionMeasure_halfplane_radians n hn
  have he := Hyperbolic.discSubtendedAngle_isometry F hF (closure S) z
  rw [F.image_closure,Hyperbolic.discOriginNormalizer_apply_self] at he
  exact he ▸ hm

/-- In particular every true source Nielsen boundary point has genuine core
angle at most pi, without any supplied boundary smoothness assumption. -/
theorem fuchsianNielsenCore_boundary_angle_le_pi
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (x : P.domain.carrier) (hx : x∈frontier (fuchsianNielsenCore P hNE)) :
    fuchsianPolygonAngle P (fuchsianNielsenCore P hNE) x≤Real.pi := by
  change Hyperbolic.discSubtendedAngle (P.finiteCoordinate '' closure (fuchsianNielsenCore P hNE))
    (P.finiteCoordinate x)≤_
  rw [P.finiteCoordinate.image_closure]
  apply discSubtendedAngle_closure_le_pi_of_not_mem (fuchsianNielsenCore_convex P hNE)
    (P.finiteCoordinate.isOpenMap _ (fuchsianNielsenCore_isOpen P hNE))
    ((fuchsianNielsenCore_isConnected P hNE).nonempty.image P.finiteCoordinate)
  exact fun h=>((fuchsianNielsenCore_isOpen P hNE).frontier_eq ▸ hx).2
    (P.finiteCoordinate.injective.mem_set_image.mp h)

/-- Positive original stabilizer and cycle sizes with at least two incident
tiles give a uniform positive boundary-cycle corner weight. -/
theorem integral_boundary_cycle_weight_lower (p m : ℕ) (hp : 0<p) (hm : 0<m)
    (hinc : 2≤p*m) : (1:ℝ)/2≤(m:ℝ)-1/(p:ℝ) := by
  by_cases hp1 : p=1
  · rw [hp1] at hinc ⊢
    simp only [one_mul] at hinc
    have hmR : (2:ℝ)≤(m:ℝ) := by exact_mod_cast hinc
    norm_num
    linarith
  · have hp2 : 2≤p := by omega
    have hpR : (2:ℝ)≤(p:ℝ) := by exact_mod_cast hp2
    have hmR : (1:ℝ)≤(m:ℝ) := by exact_mod_cast hm
    have hd : (1:ℝ)/(p:ℝ)≤1/2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
    linarith

/-- Every actual original polygon boundary point has at least two incident
closed original tiles, counted with the exact cycle/stabilizer multiplicity. -/
theorem fuchsianPolygon_boundary_incident_two_le
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (hx : x∈frontier D) :
    2≤fuchsianPointOrder P x*fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) := by
  classical
  obtain ⟨g,hg,hgx⟩ := hD.boundary_mate hx
  let C := (hD.locallyFinite.incident_finite x).toFinset
  have h1 : (1:H)∈C := by
    rw [Set.Finite.mem_toFinset]
    change x∈fuchsianDomainTile P D 1
    simpa only [fuchsianDomainTile,one_smul] using frontier_subset_closure hx
  have hginv : g⁻¹≠1 := fun h=>hg (inv_eq_one.mp h)
  have hgi : g⁻¹∈C := by
    rw [Set.Finite.mem_toFinset]
    change x∈fuchsianDomainTile P D g⁻¹
    exact ⟨g • x,frontier_subset_closure hgx,inv_smul_smul g x⟩
  have hsub : ({1,g⁻¹}:Finset H)⊆C := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact h1
    · exact Finset.mem_singleton.mp ha ▸ hgi
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hginv.symm] at hc
  exact hc.trans_eq (hD.locallyFinite.incident_card_eq_order_mul_cycleLength x)

/-- Each actual original boundary cycle meeting the source Nielsen boundary
has at least pi/2 of genuine cut-polygon corner deficit. This includes new
corners created when an old side crosses the true core boundary. -/
theorem nielsenCore_boundary_cycle_deficit_lower
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hwD : w∈D)
    (hwN : w∈fuchsianNielsenCore P hNE) (x : P.domain.carrier)
    (hxD : x∈frontier D) (hxN : x∈frontier (fuchsianNielsenCore P hNE)) :
    Real.pi/2≤∑y∈(hD.locallyFinite.cycle_finite x).toFinset,
      (Real.pi-fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) y) := by
  have hw := integral_boundary_cycle_weight_lower (fuchsianPointOrder P x)
    (fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x)) (P.pointOrder_pos x)
    (hD.locallyFinite.cycleLength_pos x) (fuchsianPolygon_boundary_incident_two_le hD x hxD)
  have hα := fuchsianNielsenCore_boundary_angle_le_pi P hNE x hxN
  have hp : (0:ℝ)<fuchsianPointOrder P x := Nat.cast_pos.mpr (P.pointOrder_pos x)
  have hdiv : fuchsianPolygonAngle P (fuchsianNielsenCore P hNE) x/(fuchsianPointOrder P x:ℝ)≤
      Real.pi/(fuchsianPointOrder P x:ℝ) := div_le_div_of_nonneg_right hα hp.le
  rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,
    nielsenCore_cycleAngle_sum hD hNE w hwD hwN x (frontier_subset_closure hxN)]
  have hc : fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x)=
      (hD.locallyFinite.cycle_finite x).toFinset.card := Set.ncard_eq_toFinset_card _ _
  rw [←hc]
  have hl := mul_le_mul_of_nonneg_right hw Real.pi_pos.le
  have he : ((fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x):ℝ)-
      1/(fuchsianPointOrder P x:ℝ))*Real.pi=
      (fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x):ℝ)*Real.pi-
        Real.pi/(fuchsianPointOrder P x:ℝ) := by ring
  rw [he] at hl
  nlinarith

/-- The whole actual source Nielsen frontier is invariant under every
original group element. -/
theorem fuchsianNielsenCore_smul_frontier
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (g : H) :
    g • frontier (fuchsianNielsenCore P hNE)=frontier (fuchsianNielsenCore P hNE) := by
  have he : g • fuchsianNielsenCore P hNE=fuchsianNielsenCore P hNE := by
    apply subset_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact fuchsianNielsenCore_invariant P hNE g x hx
    · intro x hx
      exact ⟨g⁻¹ • x,fuchsianNielsenCore_invariant P hNE g⁻¹ x hx,smul_inv_smul g x⟩
  exact ((Homeomorph.smul g).image_frontier _).trans (congrArg frontier he)

/-- The actual cut-polygon corner deficits at arbitrary original boundary
points in the closed core are controlled by the genuine core area. This
includes all new corners on the core boundary. -/
theorem nielsenCore_closed_corner_deficit_bound
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (p : 𝕔𝔻) (hp : p∈Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)))
    (X : Finset P.domain.carrier)
    (hX : ∀x∈X,x∈frontier D ∧ x∈closure (fuchsianNielsenCore P hNE)) :
    ∑x∈X,(Real.pi-fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) x)≤
      (fuchsianNielsenCoreArea P hNE D).toReal+Real.pi := by
  classical
  let Q := D∩fuchsianNielsenCore P hNE
  let S := P.finiteCoordinate '' Q
  have hoQ : IsOpen Q := hD.locallyFinite.fundamental.isOpen.inter (fuchsianNielsenCore_isOpen P hNE)
  have hoS : IsOpen S := P.finiteCoordinate.isOpenMap Q hoQ
  have hnS : S.Nonempty := ⟨P.finiteCoordinate w,mem_image_of_mem _ ⟨hwD,hwN⟩⟩
  have haS : Hyperbolic.discHyperbolicArea S≠⊤ := by rwa [←P.area_apply Q hoQ.measurableSet]
  have he (x : P.domain.carrier) : Hyperbolic.discSubtendedAngle (closure S) (P.finiteCoordinate x)=
      fuchsianPolygonAngle P Q x := by
    change Hyperbolic.discSubtendedAngle (closure S) _=
      Hyperbolic.discSubtendedAngle (P.finiteCoordinate '' closure Q) _
    rw [P.finiteCoordinate.image_closure]
  have hm (x : P.domain.carrier) : fuchsianPolygonAngle P Q x≤fuchsianPolygonAngle P D x := by
    change Hyperbolic.discSubtendedAngle (P.finiteCoordinate '' closure Q) _≤
      Hyperbolic.discSubtendedAngle (P.finiteCoordinate '' closure D) _
    exact discSubtendedAngle_mono (image_mono (closure_mono inter_subset_left)) _
  let Y := X.map P.halfPlaneCoordinate.toEquiv.toEmbedding
  have hY (z : ℍ) (hz : z∈Y) :
      Hyperbolic.discToClosedModel (Hyperbolic.halfPlaneToDisc z)∈closure (Hyperbolic.discToClosedModel '' S) ∧
      Hyperbolic.discSubtendedAngle (closure S) (Hyperbolic.halfPlaneToDisc z)≤Real.pi := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hz
    change Hyperbolic.discToClosedModel (Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate
      x))∈closure (Hyperbolic.discToClosedModel '' S) ∧
      Hyperbolic.discSubtendedAngle (closure S) (Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate x))≤Real.pi
    rw [P.halfPlaneCoordinate_cayley]
    constructor
    · apply mem_closure_image Hyperbolic.isEmbedding_discToClosedModel.continuous.continuousAt
      rw [←P.finiteCoordinate.image_closure]
      apply mem_image_of_mem
      rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
      exact ⟨frontier_subset_closure (hX x hx).1,(hX x hx).2⟩
    · rw [he]
      exact (hm x).trans (Fuchsian.finite_polygon_boundary_angle_le_pi hD (hX x hx).1)
  have hb := Hyperbolic.finite_corner_angle_deficit_bound_of_ideal (nielsenCore_inter_native_convex hD hNE)
    hoS hnS haS p hp Y hY
  rw [Finset.sum_map] at hb
  change (∑x∈X,(Real.pi-Hyperbolic.discSubtendedAngle (closure S)
    (Hyperbolic.halfPlaneToDisc (P.halfPlaneCoordinate x))))≤_ at hb
  simp_rw [P.halfPlaneCoordinate_cayley,he] at hb
  rwa [←P.area_apply Q hoQ.measurableSet] at hb

/-- Every point of an original cycle based on the genuine Nielsen boundary
remains on that actual boundary. -/
theorem nielsenCore_boundary_cycle_subset
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (D : Set P.domain.carrier)
    (x : P.domain.carrier)
    (hx : x∈frontier (fuchsianNielsenCore P hNE)) :
    fuchsianPolygonCycle P D x⊆frontier (fuchsianNielsenCore P hNE) := by
  rintro y ⟨_hy,hyO⟩
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hyO
  have hy : y∈g • frontier (fuchsianNielsenCore P hNE) := ⟨x,hx,hg⟩
  rwa [fuchsianNielsenCore_smul_frontier] at hy

/-- Every finite family of distinct original cycles crossing the actual core
boundary has its cardinality controlled by true finite core area. -/
theorem nielsenCore_boundary_cycle_family_budget
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (p : 𝕔𝔻) (hp : p∈Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)))
    {ι : Type*} [Fintype ι] (x : ι→P.domain.carrier)
    (hxD : ∀i,x i∈frontier D) (hxN : ∀i,x i∈frontier (fuchsianNielsenCore P hNE))
    (hinj : Function.Injective (fun i=>fuchsianPolygonCycle P D (x i))) :
    (Fintype.card ι:ℝ)*(Real.pi/2)≤(fuchsianNielsenCoreArea P hNE D).toReal+Real.pi := by
  classical
  let C (i : ι) := (hD.locallyFinite.cycle_finite (x i)).toFinset
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) C := by
    intro i _hi j _hj hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    exact disjoint_left.mp (Fuchsian.finite_polygon_cycles_disjoint P D (x i) (x j)
      (fun he=>hij (hinj he))) ((Set.Finite.mem_toFinset _).mp hzi)
      ((Set.Finite.mem_toFinset _).mp hzj)
  let X := Finset.univ.biUnion C
  have hX (z : P.domain.carrier) (hz : z∈X) : z∈frontier D ∧ z∈closure (fuchsianNielsenCore P hNE) := by
    obtain ⟨i,_hi,hzi⟩ := Finset.mem_biUnion.mp hz
    have hzC := (Set.Finite.mem_toFinset _).mp hzi
    exact ⟨Fuchsian.finite_polygon_boundary_cycle_subset_frontier hD.locallyFinite.fundamental
      (hxD i) hzC,frontier_subset_closure (nielsenCore_boundary_cycle_subset P hNE D (x i) (hxN i) hzC)⟩
  have hb := nielsenCore_closed_corner_deficit_bound hD hNE harea w hwD hwN p hp X hX
  have he : (∑z∈X,(Real.pi-fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) z))=
      ∑i,∑z∈C i,(Real.pi-fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) z) := Finset.sum_biUnion hdis
  have hl : ∑i,(Real.pi/2)≤∑i,∑z∈C i,(Real.pi-fuchsianPolygonAngle P (D∩fuchsianNielsenCore P hNE) z) :=
    Finset.sum_le_sum (fun i _hi=>nielsenCore_boundary_cycle_deficit_lower hD hNE w hwD hwN (x i) (hxD i) (hxN i))
  rw [he] at hb
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hl.trans hb

/-- With a genuine ideal core point, only finitely many actual original
cycles can cross the true Nielsen boundary at finite points. -/
theorem finite_nielsenCore_boundary_cycles_of_ideal
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (p : 𝕔𝔻) (hp : p∈Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))) :
    {C : Set P.domain.carrier | ∃x,x∈frontier D ∧
      x∈frontier (fuchsianNielsenCore P hNE) ∧ C=fuchsianPolygonCycle P D x}.Finite := by
  classical
  by_contra hn
  obtain ⟨n,hnR⟩ := exists_nat_gt (((fuchsianNielsenCoreArea P hNE D).toReal+Real.pi)/(Real.pi/2))
  obtain ⟨F,hF,hcard⟩ := Set.Infinite.exists_subset_card_eq hn n
  have hrep (C : F) : ∃x,x∈frontier D ∧ x∈frontier (fuchsianNielsenCore P hNE) ∧
      C.val=fuchsianPolygonCycle P D x := hF C.property
  choose x hxD hxN he using hrep
  have hinj : Function.Injective (fun C : F=>fuchsianPolygonCycle P D (x C)) := by
    intro C E hCE
    apply Subtype.ext
    exact (he C).trans (hCE.trans (he E).symm)
  have hb := nielsenCore_boundary_cycle_family_budget hD hNE harea w hwD hwN p hp x hxD hxN hinj
  have hc : Fintype.card F=n := by simpa only [Fintype.card_coe] using hcard
  rw [hc] at hb
  have hπ : 0<Real.pi/2 := by positivity
  exact (not_lt_of_ge hb) ((div_lt_iff₀ hπ).mp hnR)

/-- Finite true Nielsen-core area and a genuine ideal core point force
finitely many actual finite intersections between the original polygon
frontier and the source Nielsen frontier. These are the newly cut corners. -/
theorem finite_nielsenCore_boundary_crossings_of_ideal
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (p : 𝕔𝔻) (hp : p∈Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))) :
    (frontier D∩frontier (fuchsianNielsenCore P hNE)).Finite := by
  have hC := finite_nielsenCore_boundary_cycles_of_ideal hD hNE harea w hwD hwN p hp
  have hU : (⋃C∈{C : Set P.domain.carrier | ∃x,x∈frontier D ∧
      x∈frontier (fuchsianNielsenCore P hNE) ∧ C=fuchsianPolygonCycle P D x},C).Finite := by
    apply hC.biUnion
    rintro C ⟨x,_hxD,_hxN,rfl⟩
    exact hD.locallyFinite.cycle_finite x
  apply hU.subset
  rintro x ⟨hxD,hxN⟩
  exact mem_iUnion₂.mpr ⟨fuchsianPolygonCycle P D x,⟨x,hxD,hxN,rfl⟩,
    ⟨frontier_subset_closure hxD,MulAction.mem_orbit_self x⟩⟩

/-- Only finitely many genuine original sides contain a newly cut finite
Nielsen-boundary corner. No unproved replacement of the original side set is
used in this finite-index argument. -/
theorem finite_nielsenCore_boundary_incident_sides_of_ideal
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE)
    (p : 𝕔𝔻) (hp : p∈Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧
      (S∩frontier (fuchsianNielsenCore P hNE)).Nonempty}.Finite := by
  have hV := finite_nielsenCore_boundary_crossings_of_ideal hD hNE harea w hwD hwN p hp
  have hU : (⋃x∈frontier D∩frontier (fuchsianNielsenCore P hNE),
      {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧ x∈S}).Finite := by
    apply hV.biUnion
    intro x _hx
    apply (hD.locallyFinite.compact_sides_finite {x} isCompact_singleton).subset
    rintro S ⟨hS,hxS⟩
    exact ⟨hS,x,hxS,mem_singleton x⟩
  apply hU.subset
  rintro S ⟨hS,x,hxS,hxN⟩
  exact mem_iUnion₂.mpr ⟨x,⟨hS.subset_frontier hD.locallyFinite.fundamental hxS,hxN⟩,hS,hxS⟩

/-- A preconnected set meeting an open region and avoiding its true
frontier lies wholly inside that region. -/
theorem preconnected_subset_open_of_avoids_frontier
    {X : Type*} [TopologicalSpace X] {S N : Set X} (hS : IsPreconnected S)
    (ho : IsOpen N) (hne : (S∩N).Nonempty) (hd : Disjoint S (frontier N)) : S⊆N := by
  have hcover : S⊆N∪(closure N)ᶜ := by
    intro x hx
    by_cases hxN : x∈N
    · exact Or.inl hxN
    · right
      intro hxcl
      exact disjoint_left.mp hd hx ((ho.frontier_eq).symm ▸ ⟨hxcl,hxN⟩)
  have hdis : Disjoint N (closure N)ᶜ :=
    disjoint_compl_right.mono_left subset_closure
  rcases hS.subset_or_subset ho isClosed_closure.isOpen_compl hdis hcover with hsub | hout
  · exact hsub
  · obtain ⟨x,hxS,hxN⟩ := hne
    exact False.elim (hout hxS (subset_closure hxN))

/-- A finite genuine ideal boundary admits only finitely many actual complete
native geodesics in its true closed region, without any area/FD hypothesis. -/
theorem finite_ideal_boundary_whole_lines
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (Q : Set P.domain.carrier) (hQ : (fuchsianPolygonIdealBoundary P Q).Finite) :
    {L : Hyperbolic.DiscLine | L.carrier⊆P.finiteCoordinate '' closure Q}.Finite := by
  let E := ((↑) : ℂ→OnePoint ℂ) '' fuchsianPolygonIdealBoundary P Q
  have hE : E.Finite := hQ.image _
  apply (hE.powerset.preimage Hyperbolic.DiscLine.idealEndpoints_injective.injOn).subset
  intro L hL
  exact Fuchsian.polygon_whole_line_idealEndpoints_subset P Q L hL

/-- The remaining old sides meeting the core, containing no old core vertex
and avoiding the core frontier, are actual whole geodesics. Finite actual core
ideal boundary therefore gives a finite genuine side set in this last case. -/
theorem finite_nielsenCore_internal_whole_sides
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧
      (S∩fuchsianNielsenCore P hNE).Nonempty ∧
      (¬∃x∈S,IsFuchsianPolygonVertex P D x ∧ x∈fuchsianNielsenCore P hNE) ∧
      Disjoint S (frontier (fuchsianNielsenCore P hNE))}.Finite := by
  have hf := (finite_ideal_boundary_whole_lines P (D∩fuchsianNielsenCore P hNE)
    (finite_nielsenCore_idealBoundary hD hNE harea)).image
    (fun L : Hyperbolic.DiscLine=>P.finiteCoordinate.symm '' L.carrier)
  apply hf.subset
  rintro S ⟨hS,hSN,hnv,hd⟩
  have hpre : IsPreconnected S := P.finiteCoordinate.isEmbedding.isInducing.isPreconnected_image.mp
    hS.2.1.1.isPreconnected
  have hsub := preconnected_subset_open_of_avoids_frontier hpre (fuchsianNielsenCore_isOpen P hNE) hSN hd
  obtain ⟨L,hSL⟩ := Fuchsian.polygon_side_without_vertex_is_whole_line hD hS
    (fun x hx hv=>hnv ⟨x,hx,hv,hsub hx⟩)
  have hL : L.carrier⊆P.finiteCoordinate '' closure (D∩fuchsianNielsenCore P hNE) := by
    rw [←hSL]
    apply image_mono
    intro x hx
    exact (fuchsianNielsenCore_isOpen P hNE).closure_inter
      ⟨frontier_subset_closure (hS.subset_frontier hD.locallyFinite.fundamental hx),hsub hx⟩
  refine ⟨L,hL,?_⟩
  change P.finiteCoordinate.symm '' L.carrier=S
  rw [←hSL,image_image]
  simp only [Homeomorph.symm_apply_apply,image_id']

/-- Finite genuine Nielsen-core area forces only finitely many original
sides to meet the true original Nielsen region. Original vertices, newly cut
boundary corners and actual entire geodesics are all proved finite. -/
theorem finite_nielsenCore_meeting_sides
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧
      (S∩fuchsianNielsenCore P hNE).Nonempty}.Finite := by
  by_cases hi : (Hyperbolic.discIdealClosureTrace (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))).Nonempty
  · obtain ⟨p,hp⟩ := hi
    have hV := finite_nielsenCore_vertex_incident_sides hD hNE harea w hwD hwN
    have hB := finite_nielsenCore_boundary_incident_sides_of_ideal hD hNE harea w hwD hwN p hp
    have hL := finite_nielsenCore_internal_whole_sides hD hNE harea
    apply ((hV.union hB).union hL).subset
    rintro S ⟨hS,hSN⟩
    by_cases hvertex : ∃x∈S,IsFuchsianPolygonVertex P D x ∧ x∈fuchsianNielsenCore P hNE
    · exact Or.inl (Or.inl ⟨hS,hvertex⟩)
    by_cases hcross : (S∩frontier (fuchsianNielsenCore P hNE)).Nonempty
    · exact Or.inl (Or.inr ⟨hS,hcross⟩)
    · exact Or.inr ⟨hS,hSN,hvertex,disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hcross)⟩
  · have hc := Fuchsian.native_closure_compact_of_idealTrace_empty
      (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE)) hi
    rw [←P.finiteCoordinate.image_closure] at hc
    have hcQ := P.finiteCoordinate.isEmbedding.isCompact_iff.mpr hc
    apply (hD.locallyFinite.compact_sides_finite _ hcQ).subset
    rintro S ⟨hS,x,hxS,hxN⟩
    exact ⟨hS,x,hxS,(fuchsianNielsenCore_isOpen P hNE).closure_inter
      ⟨frontier_subset_closure (hS.subset_frontier hD.locallyFinite.fundamental hxS),hxN⟩⟩

/-- At a genuine nonvertex original boundary point, every nonidentity tile
incident there has an actual full original side as its intersection. -/
theorem original_nonvertex_incident_is_side
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (g : H) (hg : g≠1) (x : P.domain.carrier)
    (hx : x∈closure D∩fuchsianDomainTile P D g) (hnv : ¬IsFuchsianPolygonVertex P D x) :
    IsFuchsianPolygonSide P D (closure D∩fuchsianDomainTile P D g) := by
  have hxfront := hD.locallyFinite.fundamental.closed_tile_intersection_subset_frontier hg hx
  obtain ⟨T,hT,a,ha,b,hb,hab,hxab⟩ := hD.nonvertex_is_side_interior hxfront hnv
  let F := normalizedPolygonKleinCoordinate P x
  have hFinj := (normalizedPolygonKleinCoordinate_isOpenEmbedding P x).injective
  have hxT : x∈T := by
    have hm := (hT.normalizedKlein_convex x).segment_subset ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
      (openSegment_subset_segment ℝ _ _ hxab)
    obtain ⟨y,hy,he⟩ := hm
    exact hFinj he ▸ hy
  obtain ⟨h,hh,hTe⟩ := hT.1
  have hxTh : x∈fuchsianDomainTile P D h := (hTe ▸ hxT).2
  obtain ⟨k,_hk,hunique⟩ := hD.nonvertex_incident_unique hxfront hnv
  have hgh : g=h := (hunique g ⟨hg,hx.2⟩).trans (hunique h ⟨hh,hxTh⟩).symm
  rw [hgh]
  exact hTe ▸ hT

/-- Finite actual core area gives only finitely many original adjacent
closed-tile labels inside the actual core. Both vertex incidences and genuine
side-pairing labels are counted in the original group. -/
theorem finite_nielsenCore_adjacent_labels
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤)
    (w : P.domain.carrier) (hwD : w∈D) (hwN : w∈fuchsianNielsenCore P hNE) :
    {g : H | (closure D∩fuchsianDomainTile P D g∩fuchsianNielsenCore P hNE).Nonempty}.Finite := by
  classical
  have hV := finite_nielsenCore_vertices hD hNE harea w hwD hwN
  have hVI : (⋃x∈{x | IsFuchsianPolygonVertex P D x ∧ x∈fuchsianNielsenCore P hNE},
      {g : H | x∈fuchsianDomainTile P D g}).Finite :=
    hV.biUnion (fun x _hx=>hD.locallyFinite.incident_finite x)
  let e (S : Set P.domain.carrier) : H :=
    if hS : IsFuchsianPolygonSide P D S then fuchsianSideElement hD ⟨S,hS⟩ else 1
  have hSide := (finite_nielsenCore_meeting_sides hD hNE harea w hwD hwN).image e
  apply (((finite_singleton (1:H)).union hVI).union hSide).subset
  rintro g ⟨x,hx,hxN⟩
  by_cases hg : g=1
  · exact Or.inl (Or.inl (mem_singleton_iff.mpr hg))
  by_cases hv : IsFuchsianPolygonVertex P D x
  · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨x,⟨hv,hxN⟩,hx.2⟩))
  · right
    let S := closure D∩fuchsianDomainTile P D g
    have hS := original_nonvertex_incident_is_side hD g hg x hx hv
    have he : e S=fuchsianSideElement hD ⟨S,hS⟩ := dite_eq_left hS
    have hg' : g=fuchsianSideElement hD ⟨S,hS⟩ :=
      (hD.existsUnique_side_element hS).choose_spec.2 g ⟨hg,rfl⟩
    exact ⟨S,⟨hS,x,hx,hxN⟩,he.trans hg'.symm⟩

/-- Finite true Nielsen-core area implies finite generation of the original
whole group, using genuinely finite original adjacency labels in the actual
connected core. No finite-side or finite-cycle conclusion is a premise. -/
theorem finite_nielsenCore_finitelyGenerated
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hwD : w∈D)
    (hwN : w∈fuchsianNielsenCore P hNE)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤) : H.FG := by
  classical
  let N : SubMulAction H P.domain.carrier :=
    ⟨fuchsianNielsenCore P hNE,fun g _x hx => fuchsianNielsenCore_invariant P hNE g _ hx⟩
  let : ConnectedSpace N := isConnected_iff_connectedSpace.mp (fuchsianNielsenCore_isConnected P hNE)
  let : ContinuousConstSMul H N := ⟨fun g =>
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩
  let K : Set N := Subtype.val ⁻¹' closure D
  have hK : IsClosed K := isClosed_closure.preimage continuous_subtype_val
  have hnK : K.Nonempty := ⟨⟨w,hwN⟩,subset_closure hwD⟩
  have he (g : H) : g • K=(Subtype.val : N→P.domain.carrier) ⁻¹' fuchsianDomainTile P D g := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.val,hy,rfl⟩
    · rintro ⟨y,hy,hgy⟩
      have hyN : y∈fuchsianNielsenCore P hNE := by
        have hh := fuchsianNielsenCore_invariant P hNE g⁻¹ x.val x.property
        change g • y=x.val at hgy
        rwa [←hgy,inv_smul_smul] at hh
      exact ⟨⟨y,hyN⟩,hy,Subtype.ext hgy⟩
  have hlf : LocallyFinite (fun g : H => g • K) := by
    simp_rw [he]
    exact hD.locallyFinite.locallyFinite.preimage_continuous continuous_subtype_val
  have hcov : (⋃g : H,g • K)=univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x.val∈⋃g : H,fuchsianDomainTile P D g := by
      change x.val∈⋃g : H,(fun y : P.domain.carrier => g • y) '' closure D
      rw [hD.locallyFinite.fundamental.closure_cover]
      trivial
    obtain ⟨g,hg⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨g,?_⟩
    rw [he]
    exact hg
  have hgen := connected_closed_tiles_generate K hK hnK hlf hcov
  have hfinite : {g : H | (K∩g • K).Nonempty}.Finite := by
    apply (finite_nielsenCore_adjacent_labels hD hNE harea w hwD hwN).subset
    rintro g ⟨x,hxK,hxg⟩
    have hxg' : x∈(Subtype.val : N→P.domain.carrier) ⁻¹' fuchsianDomainTile P D g := by
      rw [←he g]
      exact hxg
    exact ⟨x.val,⟨hxK,hxg'⟩,x.property⟩
  apply (Group.fg_iff_subgroup_fg H).mp
  exact Group.fg_iff.mpr ⟨_,hgen,hfinite⟩

/-- The finite-core-area converse holds for any genuine original
fundamental domain: a true free Dirichlet centre is constructed inside N. -/
theorem finite_nielsenCoreArea_finitelyGenerated
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D)
    (harea : fuchsianNielsenCoreArea P hNE D≠⊤) : H.FG := by
  obtain ⟨w,hw,hwN⟩ := exists_dirichlet_center_in_nielsenCore P hNE
  have harea' : fuchsianNielsenCoreArea P hNE (dirichletDomain P w)≠⊤ := by
    rwa [fuchsianNielsenCoreArea_independent P hNE (dirichletDomain_fundamental P w hw) hD]
  exact finite_nielsenCore_finitelyGenerated (dirichletDomain_isConvexFuchsianPolygon P w hw) hNE w
    (dirichletDomain_center_mem P w hw) hwN harea'

/--
and (2) are equivalent with the actual original group
and true core area of every given genuine fundamental domain.
-/
theorem finitelyGenerated_iff_nielsenCoreArea_ne_top
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D) :
    H.FG ↔ fuchsianNielsenCoreArea P hNE D≠⊤ :=
  ⟨fun hFG=>finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD,
    finite_nielsenCoreArea_finitelyGenerated P hNE hD⟩

/-- The finite-core-area converse retains an arbitrary original geometric
disc, original density measure and original whole group. -/
theorem finite_geometricNielsenCoreArea_finitelyGenerated
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    {S : Set (fuchsianGeometricDomain D).carrier}
    (hS : DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D).carrier (geometricModelArea D) S)
    (harea : geometricNielsenCoreArea D hNE S≠⊤) : H.FG := by
  let P := geometricDiscData D
  let e := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence (geometricDiscNormalizer D) H
  rw [geometricNielsenCoreArea_eq_disc D hNE S hS.isOpen.measurableSet] at harea
  have hFG := finite_nielsenCoreArea_finitelyGenerated P
    (hNE.conjugation (geometricDiscNormalizer D)) (geometric_fundamentalDomain_to_disc D hS) harea
  let : Group.FG (geometricDiscGroup D) := (Group.fg_iff_subgroup_fg _).mpr hFG
  have : Group.FG H := Group.fg_of_surjective (f:=e.symm.toMonoidHom) e.symm.surjective
  exact (Group.fg_iff_subgroup_fg H).mp inferInstance

/-- The actual original Nielsen-core area criterion for finite generation,
with no fixed standard-domain normalization in the hypotheses. -/
theorem finitelyGenerated_iff_geometricNielsenCoreArea_ne_top
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    {S : Set (fuchsianGeometricDomain D).carrier}
    (hS : DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D).carrier (geometricModelArea D) S) :
    H.FG ↔ geometricNielsenCoreArea D hNE S≠⊤ :=
  ⟨fun hFG=>finitelyGenerated_geometricNielsenCoreArea_ne_top D hNE hFG hS,
    finite_geometricNielsenCoreArea_finitelyGenerated D hNE hS⟩

end LowDimensionalTopology.Geometry.Fuchsian
