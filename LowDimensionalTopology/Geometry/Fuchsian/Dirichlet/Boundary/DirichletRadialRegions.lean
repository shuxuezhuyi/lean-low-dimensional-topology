module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.ConvexRadial
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.ConvexRadialEnds
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.JordanFrontierSeparation
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian

/-- A genuine continuous surjective open map with connected actual fibers has
connected total space when its actual target is connected. -/
theorem connectedSpace_of_open_surjective_connected_fibers
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace Y]
    {f : X → Y} (hc : Continuous f) (ho : IsOpenMap f) (hs : Function.Surjective f)
    (hf : ∀ y : Y, IsConnected (f ⁻¹' {y})) : ConnectedSpace X := by
  apply connectedSpace_iff_univ.mpr
  simpa only [preimage_univ] using
    (ho.isQuotientMap hc hs).isCoinducing.isConnected_preimage_of_isClosed
      hf isClosed_univ isConnected_univ

/-- An actual open set contains a genuine short outward radial continuation of
every one of its points. -/
theorem open_ray_exists_scale_gt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {a : E} (ha : a ∈ U) :
    ∃ s : ℝ, 1 < s ∧ s • a ∈ U := by
  have hc : Continuous (fun s : ℝ => s • a) := continuous_id.smul continuous_const
  have hn : (fun s : ℝ => s • a) ⁻¹' U ∈ 𝓝 (1:ℝ) :=
    hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa only [one_smul] using ha))
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨1+ε/2,by linarith,?_⟩
  apply hεU
  change dist (1+ε/2) 1 < ε
  rw [Real.dist_eq,show (1+ε/2)-1 = ε/2 by ring,abs_of_pos (by linarith)]
  linarith

/-- Removing the inner bounding sphere from a genuine radial end still leaves
a preconnected region. Openness of the original convex set gives true outward
fibers, and the actual open radial projection has connected fibers. -/
theorem convex_strict_radial_end_preconnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) (hUo : IsOpen U)
    (r : ℝ) (hr : 0 < r) {A : Set E} (hA : IsPreconnected A)
    (hAsub : A ⊆ U ∩ {x | ‖x‖ = r}) :
    IsPreconnected {x | x ∈ U ∧ r < ‖x‖ ∧ _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection r x ∈ A} := by
  rcases A.eq_empty_or_nonempty with he | hne
  · simp only [he,mem_empty_iff_false,and_false,ofPred_false,isPreconnected_empty]
  let : ConnectedSpace A := isConnected_iff_connectedSpace.mp (⟨hne,hA⟩ : IsConnected A)
  let W : Set (A × Ioi (1:ℝ)) := {p | p.2.val • p.1.val ∈ U}
  have hWo : IsOpen W := hUo.preimage
    ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst))
  let f : W → A := fun p => p.val.1
  have hfc : Continuous f := continuous_fst.comp continuous_subtype_val
  have hfo : IsOpenMap f :=
    isOpenMap_fst.comp hWo.isOpenEmbedding_subtypeVal.isOpenMap
  have hfs : Function.Surjective f := by
    intro a
    obtain ⟨s,hs,hsU⟩ := open_ray_exists_scale_gt_one hUo (hAsub a.property).1
    exact ⟨⟨(a,⟨s,hs⟩),hsU⟩,rfl⟩
  have hFib (a : A) : IsConnected (f ⁻¹' {a}) := by
    let T : Set ℝ := {s | 1 < s ∧ s • a.val ∈ U}
    have hTc : Convex ℝ T := by
      exact (convex_Ioi (1:ℝ)).inter (hU.linear_preimage (LinearMap.toSpanSingleton ℝ E a.val))
    have hTne : T.Nonempty := open_ray_exists_scale_gt_one hUo (hAsub a.property).1
    let : ConnectedSpace T := isConnected_iff_connectedSpace.mp (⟨hTne,hTc.isPreconnected⟩ : IsConnected T)
    let g : T → W := fun s => ⟨(a,⟨s.val,s.property.1⟩),s.property.2⟩
    have hgc : Continuous g := by
      apply Continuous.subtype_mk
      exact continuous_const.prodMk (continuous_subtype_val.subtype_mk _)
    have hrange : range g = f ⁻¹' {a} := by
      ext p
      constructor
      · rintro ⟨s,rfl⟩
        rfl
      · intro hp
        have he : p.val.1 = a := hp
        refine ⟨⟨p.val.2.val,p.val.2.property,?_⟩,?_⟩
        · rw [←he]
          exact p.property
        · apply Subtype.ext
          exact Prod.ext he.symm rfl
    rw [←hrange]
    exact isConnected_range hgc
  let : ConnectedSpace W := connectedSpace_of_open_surjective_connected_fibers hfc hfo hfs hFib
  let g : W → E := fun p => p.val.2.val • p.val.1.val
  have hgc : Continuous g :=
    ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).smul
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)))
  have hrange : range g = {x | x ∈ U ∧ r < ‖x‖ ∧ _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection r x ∈ A} := by
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      have hn : ‖p.val.1.val‖ = r := (hAsub p.val.1.property).2
      have hs : 0 < p.val.2.val := zero_lt_one.trans p.val.2.property
      refine ⟨p.property,?_,?_⟩
      · dsimp [g]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs,hn]
        have hsp : 1 < p.val.2.val := p.val.2.property
        nlinarith
      · dsimp [g]
        rw [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection,NormedSpace.normalize_smul_of_pos hs]
        change _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection r p.val.1.val ∈ A
        rw [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection_eq_self r hn]
        exact p.val.1.property
    · rintro ⟨hxU,hxr,hxp⟩
      have hs : 1 < ‖x‖/r := (one_lt_div hr).mpr hxr
      have he : (‖x‖/r) • _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection r x = x := by
        rw [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection,smul_smul,div_mul_cancel₀ _
          hr.ne',NormedSpace.norm_smul_normalize]
      refine ⟨⟨(⟨_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection r
        x,hxp⟩,⟨‖x‖/r,hs⟩),?_⟩,he⟩
      change (‖x‖/r) • _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection r x ∈ U
      rwa [he]
  rw [←hrange]
  exact isPreconnected_range hgc


/-- A true positive radial cone over an intrinsically open spherical set is
open in the original normed space. -/
theorem positive_radial_cone_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) {A : Set E} (hA : A ⊆ Metric.sphere (0:E) r)
    (hAo : IsOpen ((Subtype.val : Metric.sphere (0:E) r → E) ⁻¹' A)) :
    IsOpen ((Ioi (0:ℝ)) • A) := by
  let V : Set (Metric.sphere (0:E) r) := Subtype.val ⁻¹' A
  have hV : (V : Set E) = A := by
    change Subtype.val '' (Subtype.val ⁻¹' A) = A
    apply image_preimage_eq_of_subset
    intro x hx
    exact ⟨⟨x,hA hx⟩,rfl⟩
  have ho : IsOpen ((Ioi (0:ℝ)) • (V : Set E)) :=
    IsOpen.smul_sphere hr.ne' (isOpen_Ioi : IsOpen (Ioi (0:ℝ))) (by simp) hAo
  simpa only [hV] using ho

/-- Positive radial scaling leaves the genuine spherical projection on the
same original spherical subset. -/
theorem radialSphereProjection_mem_of_mem_positive_cone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} {A : Set E} (hA : A ⊆ {x | ‖x‖ = r})
    {x : E} (hx : x ∈ (Ioi (0:ℝ)) • A) : _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection r x ∈ A := by
  obtain ⟨s,hs,a,ha,rfl⟩ := hx
  rw [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection,NormedSpace.normalize_smul_of_pos
    hs]
  change _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection r a ∈ A
  rw [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection_eq_self r (hA ha)]
  exact ha

/-- An actual open region avoiding the inner ball, touching the spherical slice
of an original open convex set, and having no exterior frontier there, contains
the complete genuine radial end based at that slice. The side assignment is
derived from the original topology and convexity, not assumed. -/
theorem convex_strict_radial_end_subset_open_region
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) (hUo : IsOpen U)
    (r : ℝ) (hr : 0 < r) {A : Set E} (hA : IsPreconnected A)
    (hAsub : A ⊆ U ∩ {x | ‖x‖ = r})
    (hAo : IsOpen ((Subtype.val : Metric.sphere (0:E) r → E) ⁻¹' A))
    {W : Set E} (hWo : IsOpen W)
    (hWball : Disjoint W (U ∩ Metric.ball (0:E) r))
    (hWfront : frontier W ∩ U ⊆ Metric.sphere (0:E) r)
    (hcontact : (A ∩ closure W).Nonempty) :
    {x | x ∈ U ∧ r < ‖x‖ ∧ _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection r x ∈ A} ⊆ W := by
  let Q : Set E := {x | x ∈ U ∧ r < ‖x‖ ∧
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection r x ∈ A}
  have hQc : IsPreconnected Q := convex_strict_radial_end_preconnected hU hUo r hr hA hAsub
  have hAsph : A ⊆ Metric.sphere (0:E) r := by
    intro x hx
    have hn : ‖x‖ = r := (hAsub hx).2
    simpa only [Metric.mem_sphere,dist_zero_right] using hn
  have hCone : IsOpen ((Ioi (0:ℝ)) • A) := positive_radial_cone_isOpen hr hAsph hAo
  obtain ⟨a,haA,haW⟩ := hcontact
  have haCone : a ∈ (Ioi (0:ℝ)) • A := ⟨1,zero_lt_one,a,haA,one_smul ℝ a⟩
  let O : Set E := U ∩ (Ioi (0:ℝ)) • A
  have hOo : IsOpen O := hUo.inter hCone
  obtain ⟨z,hzO,hzW⟩ := mem_closure_iff.mp haW O hOo ⟨(hAsub haA).1,haCone⟩
  have hzr : r ≤ ‖z‖ := by
    by_contra he
    have hzB : z ∈ Metric.ball (0:E) r := by
      simpa only [Metric.mem_ball,dist_zero_right] using lt_of_not_ge he
    exact disjoint_left.mp hWball hzW ⟨hzO.1,hzB⟩
  obtain ⟨s,hs,hsWO⟩ := open_ray_exists_scale_gt_one (hWo.inter hOo) ⟨hzW,hzO⟩
  have hsr : r < ‖s • z‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hs)]
    nlinarith
  have hyQ : s • z ∈ Q := ⟨hsWO.2.1,hsr,
    radialSphereProjection_mem_of_mem_positive_cone (fun _ hx => (hAsub hx).2) hsWO.2.2⟩
  have hQavoid : Q ⊆ W ∪ (closure W)ᶜ := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · right
      intro hxcl
      have hxfr : x ∈ frontier W := by rw [hWo.frontier_eq]; exact ⟨hxcl,hxW⟩
      have he : ‖x‖ = r := by
        simpa only [Metric.mem_sphere,dist_zero_right] using hWfront ⟨hxfr,hx.1⟩
      exact hx.2.1.ne' he
  have hdis : Disjoint W (closure W)ᶜ := disjoint_left.mpr fun _ hx hn => hn (subset_closure hx)
  have hside := hQc.subset_or_subset hWo isClosed_closure.isOpen_compl hdis hQavoid
  exact hside.resolve_right fun hOutside => hOutside hyQ (subset_closure hsWO.1)


open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- In the original open Dirichlet polygon, every point in the actual closure
of the full orbit-ball union has true center-distance at most its radius. -/
theorem dirichlet_closure_orbitBall_radius_le
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) {x : P.domain.carrier}
    (hxD : x ∈ dirichletDomain P w) (hxN : x ∈ closure (fuchsianOrbitBallUnion P w R)) :
    P.hyperbolicDist w x ≤ R := by
  by_contra he
  have hRx : R < P.hyperbolicDist w x := lt_of_not_ge he
  let V := dirichletDomain P w ∩ {y | R < P.hyperbolicDist w y}
  have hdc : Continuous (fun y : P.domain.carrier => P.hyperbolicDist w y) :=
    continuous_const.dist P.halfPlaneCoordinate.continuous
  have hVo : IsOpen V := (dirichletDomain_isOpen P w).inter
    (isOpen_lt continuous_const hdc)
  obtain ⟨y,hyV,hyN⟩ := mem_closure_iff.mp hxN V hVo ⟨hxD,hRx⟩
  have hyD : y ∈ dirichletDomain P w := hyV.1
  have hyclD : y ∈ closure (dirichletDomain P w) := subset_closure hyD
  have hyR : P.hyperbolicDist w y < R :=
    (dirichlet_closed_mem_orbitBallUnion_iff P w R hyclD).mp hyN
  have hygt : R < P.hyperbolicDist w y := hyV.2
  exact hygt.not_gt hyR

/-- The actual orbit-neighbourhood frontier inside the original Dirichlet
polygon lies on the true original center circle. -/
theorem dirichlet_orbitBall_frontier_radius
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) {x : P.domain.carrier}
    (hxD : x ∈ dirichletDomain P w) (hxN : x ∈ frontier (fuchsianOrbitBallUnion P w R)) :
    P.hyperbolicDist w x = R := by
  apply le_antisymm (dirichlet_closure_orbitBall_radius_le P w R hxD (frontier_subset_closure hxN))
  by_contra he
  have hxR : P.hyperbolicDist w x < R := lt_of_not_ge he
  have hxBall := (dirichlet_closed_mem_orbitBallUnion_iff P w R (subset_closure hxD)).mpr hxR
  exact disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr (fuchsianOrbitBallUnion_isOpen P w R)) hxN hxBall

/-- The original strict Dirichlet exterior avoids even the true closure of the
full orbit-ball neighbourhood. -/
theorem dirichlet_strict_exterior_disjoint_closure_orbitBall
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) :
    Disjoint (dirichletDomain P w ∩ {x | R < P.hyperbolicDist w x})
      (closure (fuchsianOrbitBallUnion P w R)) := by
  apply disjoint_left.mpr
  intro x hx hxN
  exact hx.2.not_ge (dirichlet_closure_orbitBall_radius_le P w R hx.1 hxN)

/-- In the genuine normalized Klein coordinate, the actual orbit-neighbourhood
frontier within the original Dirichlet polygon lies on the literal sphere. -/
theorem dirichlet_orbitBall_frontier_normalizedKlein_sphere
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) :
    (normalizedPolygonKleinCoordinate P w '' frontier (fuchsianOrbitBallUnion P w R)) ∩
      (normalizedPolygonKleinCoordinate P w '' dirichletDomain P w) ⊆
        Metric.sphere (0:ℂ) (Real.tanh R) := by
  rintro z ⟨⟨x,hxF,rfl⟩,⟨y,hyD,hyx⟩⟩
  have hy : y = x := (normalizedPolygonKleinCoordinate_isOpenEmbedding P w).injective hyx
  have hxD : x ∈ dirichletDomain P w := hy ▸ hyD
  have hr := dirichlet_orbitBall_frontier_radius P w R hxD hxF
  simp only [Metric.mem_sphere,dist_zero_right,
    normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist,hr]


/-- The genuine radial-end assignment in the original Dirichlet polygon. An
actual open opposite region with original frontier in the true orbit frontier
contains the whole actual strict radial end once the actual spherical component
touches it. Neither region assignment nor finite ends is a hypothesis. -/
theorem dirichlet_Klein_strict_end_subset_region
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ) (hR : 0 < R)
    {A : Set ℂ} (hA : IsPreconnected A)
    (hAsub : A ⊆ (normalizedPolygonKleinCoordinate P w '' dirichletDomain P w) ∩
      {z | ‖z‖ = Real.tanh R})
    (hAo : IsOpen ((Subtype.val : Metric.sphere (0:ℂ) (Real.tanh R) → ℂ) ⁻¹' A))
    {I : Set P.domain.carrier} (hIo : IsOpen I)
    (hIN : Disjoint I (fuchsianOrbitBallUnion P w R))
    (hIfront : frontier I ⊆ frontier (fuchsianOrbitBallUnion P w R))
    (hcontact : (A ∩ closure (normalizedPolygonKleinCoordinate P w '' I)).Nonempty) :
    {x | x ∈ dirichletDomain P w ∧ R < P.hyperbolicDist w x ∧
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection (Real.tanh R) (normalizedPolygonKleinCoordinate P w x) ∈ A} ⊆ I := by
  let f := normalizedPolygonKleinCoordinate P w
  let U := f '' dirichletDomain P w
  let W := f '' I
  let r := Real.tanh R
  have hf := normalizedPolygonKleinCoordinate_isOpenEmbedding P w
  have hr : 0 < r := by
    apply lt_of_not_ge
    intro h
    have hh := (tanh_radial_order_iff R 0).mp (by simpa only [Real.tanh_zero] using h)
    exact hR.not_ge hh
  have hUo : IsOpen U := hf.isOpenMap _ (dirichletDomain_isOpen P w)
  have hUc : Convex ℝ U := by
    have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
    have hh := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex
      _).mp (hD.pointCoordinate_smul_convex w (1:H))
    change Convex ℝ ((fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      ((polygonPointCoordinate P w) x)) '' dirichletDomain P w)
    simpa only [one_smul,image_image] using hh
  have hWo : IsOpen W := hf.isOpenMap _ hIo
  have hWball : Disjoint W (U ∩ Metric.ball (0:ℂ) r) := by
    apply disjoint_left.mpr
    rintro z ⟨x,hxI,rfl⟩ ⟨⟨y,hyD,hyx⟩,hxB⟩
    have hy : y = x := hf.injective hyx
    have hxD : x ∈ dirichletDomain P w := hy ▸ hyD
    have hn : Real.tanh (P.hyperbolicDist w x) < Real.tanh R := by
      change dist (normalizedPolygonKleinCoordinate P w x) 0 < Real.tanh R at hxB
      rw [dist_zero_right,normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist] at hxB
      exact hxB
    have hxR : P.hyperbolicDist w x < R := by
      apply lt_of_not_ge
      intro he
      exact hn.not_ge ((tanh_radial_order_iff R (P.hyperbolicDist w x)).mpr he)
    have hxN := (dirichlet_closed_mem_orbitBallUnion_iff P w R (subset_closure hxD)).mpr hxR
    exact disjoint_left.mp hIN hxI hxN
  have hWfront : frontier W ∩ U ⊆ Metric.sphere (0:ℂ) r := by
    rintro z ⟨hzF,⟨x,hxD,rfl⟩⟩
    have hxF : x ∈ frontier I := by
      have hx : x ∈ f ⁻¹' frontier (f '' I) := hzF
      rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous,
        preimage_image_eq _ hf.injective] at hx
      exact hx
    exact dirichlet_orbitBall_frontier_normalizedKlein_sphere P w R
      ⟨⟨x,hIfront hxF,rfl⟩,⟨x,hxD,rfl⟩⟩
  have hAssign := convex_strict_radial_end_subset_open_region hUc hUo r hr
    hA hAsub hAo hWo hWball hWfront hcontact
  intro x hx
  have hn : r < ‖f x‖ := by
    change Real.tanh R < ‖normalizedPolygonKleinCoordinate P w x‖
    rw [normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist]
    apply lt_of_not_ge
    intro he
    exact hx.2.1.not_ge ((tanh_radial_order_iff (P.hyperbolicDist w x) R).mp he)
  have hxW : f x ∈ W := hAssign ⟨⟨x,hx.1,rfl⟩,hn,hx.2.2⟩
  obtain ⟨y,hyI,hyx⟩ := hxW
  exact hf.injective hyx ▸ hyI

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The actual original hyperbolic metric circle is the genuine Euclidean
sphere in the original normalized Klein coordinate, by a true homeomorphism. -/
def fuchsianKleinMetricCircleHomeomorph
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) :
    Circle ≃ₜ Metric.sphere (0:ℂ) (Real.tanh R) :=
  (fuchsianMetricCircleHomeomorph P w R hR).trans
    (((normalizedPolygonKleinCoordinate_isOpenEmbedding P w).isEmbedding.homeomorphImage
      {x | P.hyperbolicDist w x = R}).trans
      (Homeomorph.setCongr (normalizedPolygonKleinCoordinate_image_metric_circle P w R)))

theorem fuchsianKleinMetricCircleHomeomorph_apply_val
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) (u : Circle) :
    ((fuchsianKleinMetricCircleHomeomorph P w R hR u) : ℂ) =
      normalizedPolygonKleinCoordinate P w ((fuchsianMetricCircleHomeomorph P w R hR u).val) := rfl

namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

theorem klein_originalArc_isPreconnected (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    IsPreconnected (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x) := by
  obtain ⟨v,_hv,hvC⟩ := (d.component_spec hw x).1
  have hC : IsPreconnected (d.component hw x) := hvC ▸ isPreconnected_connectedComponentIn
  exact (hC.image _ d.coordinate_continuous.continuousOn).image _
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate_isOpenEmbedding P
      w).continuous.continuousOn

theorem klein_originalArc_isOpen_sphere (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    IsOpen ((Subtype.val : Metric.sphere (0:ℂ) (Real.tanh d.radius) → ℂ) ⁻¹'
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x)) := by
  let : LocallyConnectedSpace Circle := _root_.LowDimensionalTopology.Geometry.Fuchsian.circle_locallyConnectedSpace
  obtain ⟨v,_hv,hvC⟩ := (d.component_spec hw x).1
  have hCo : IsOpen (d.component hw x) := hvC ▸ d.region_isOpen.connectedComponentIn
  let e := _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianKleinMetricCircleHomeomorph P w d.radius d.radius_pos
  have hEq : (Subtype.val : Metric.sphere (0:ℂ) (Real.tanh d.radius) → ℂ) ⁻¹'
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x) = e '' d.component hw x := by
    ext z
    constructor
    · rintro ⟨y,⟨u,hu,rfl⟩,hyz⟩
      refine ⟨u,hu,Subtype.ext ?_⟩
      exact hyz
    · rintro ⟨u,hu,rfl⟩
      exact ⟨d.coordinate u,⟨u,hu,rfl⟩,rfl⟩
  rw [hEq]
  exact e.isOpenMap _ hCo

theorem klein_originalArc_subset_spherical_slice (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter
  P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x ⊆
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w ''
        _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w) ∩
        {z | ‖z‖ = Real.tanh d.radius} := by
  rintro z ⟨y,hy,rfl⟩
  refine ⟨⟨y,d.originalArc_subset_dirichlet hw x hy,rfl⟩,?_⟩
  obtain ⟨u,hu,rfl⟩ := hy
  change ‖_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w (d.coordinate
    u)‖ = Real.tanh d.radius
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist]
  exact congrArg Real.tanh (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianMetricCircleHomeomorph P w d.radius
    d.radius_pos u).property

end RegularDirichletCircleData
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The true finite chart pulls a genuine complex Jordan frontier back to the
actual frontier of its original-disc bounded region. -/
theorem unitDisc_inside_preimage_frontier_eq
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {C : Set ℂ} (hC : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C) :
    frontier ((fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) ⁻¹'
      _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) =
      (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) ⁻¹' C := by
  have hf := unitDisc_finite_plane_isOpenEmbedding P
  rw [←hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous,
    (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hC).2.2.2.2.2.2.1]

/-- An original neighbourhood on the true outside is disjoint from the actual
original-disc preimage of the bounded Jordan side. -/
theorem unitDisc_inside_preimage_disjoint_of_outside
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {C : Set ℂ} (hC : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C) {N : Set P.domain.carrier}
    (hN : (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) '' N ⊆
      _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside C) :
    Disjoint ((fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) N := by
  apply disjoint_left.mpr
  intro x hxI hxN
  exact disjoint_left.mp (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hC).2.2.1 hxI (hN
    ⟨x,hxN,rfl⟩)

/-- A genuine original-disc Jordan circle gives an actual open opposite region
with compact closure in the original disc and exactly that genuine frontier. -/
theorem unitDisc_finite_circle_inside_preimage_properties
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {J : Circle → P.domain.carrier} (hJ : Continuous J) (hJi : Function.Injective J) :
    let C := range (fun u => (P.finiteCoordinate (J u):ℂ))
    let I := (fun z : P.domain.carrier => (P.finiteCoordinate
      z:ℂ)) ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
    IsOpen I ∧ IsCompact (closure I) ∧ frontier I = range J := by
  let f := fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)
  let C := range (fun u => f (J u))
  let I := f ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
  have hf := unitDisc_finite_plane_isOpenEmbedding P
  have hC : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C := unitDisc_injective_circle_isComplexJordanCurve P hJ hJi
  have hIo : IsOpen I := (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions
    hC).1.preimage hf.continuous
  have hIcl : closure I ⊆ f ⁻¹' closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) :=
    closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage hf.continuous)
  refine ⟨hIo,(unitDisc_Jordan_inside_closure_preimage_compact P hJ).of_isClosed_subset
    isClosed_closure hIcl,?_⟩
  rw [unitDisc_inside_preimage_frontier_eq P hC]
  ext x
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨u,hf.injective hu⟩
  · rintro ⟨u,rfl⟩
    exact ⟨u,rfl⟩

namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

theorem originalArc_nonempty (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    (d.originalArc hw x).Nonempty := by
  obtain ⟨v,hv,hvC⟩ := (d.component_spec hw x).1
  refine ⟨d.coordinate v,⟨v,?_,rfl⟩⟩
  rw [←hvC]
  exact mem_connectedComponentIn hv

/-- Every genuine finite-return original cut has a true whole strict radial end
contained in an actual open region with compact closure in the original disc.
The statement keeps only the original group, center and actual return hypotheses. -/
theorem finite_period_radial_end_precompact
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hw :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hpos : 0 < d.endpointPeriod
      hw x) :
    ∃ I : Set P.domain.carrier, IsOpen I ∧ IsCompact (closure I) ∧
      {z | z ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w ∧ d.radius < P.hyperbolicDist w z ∧
        _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection (Real.tanh
          d.radius) (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z) ∈
          _root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x} ⊆ I := by
  obtain ⟨J,hJ,hJi,hJrange,hJfront,hNout,_hCompact⟩ := d.finite_period_neighborhood_outside hNE hw x hpos
  let f := fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)
  let C := range (fun u => f (J u))
  let I := f ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
  have hC : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C := _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_injective_circle_isComplexJordanCurve P hJ hJi
  obtain ⟨hIo,hIc,hIfr⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_finite_circle_inside_preimage_properties P hJ hJi
  have hIN : Disjoint I (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_inside_preimage_disjoint_of_outside P hC hNout
  have hIfront : frontier I ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
    rw [hIfr]
    exact hJfront
  have hArcJ : d.originalArc hw x ⊆ range J := by
    intro z hz
    rw [hJrange]
    apply mem_iUnion₂.mpr
    refine ⟨0,hpos,?_⟩
    have hC0 : d.developedClosedArc hw x 0 = closure (d.originalArc hw x) := by
      simp only [developedClosedArc,state,pow_zero,Equiv.Perm.one_apply,one_smul]
    rw [hC0]
    exact subset_closure hz
  have hcontact :
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x) ∩
        closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' I)).Nonempty := by
    obtain ⟨z,hz⟩ := d.originalArc_nonempty hw x
    refine ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z,⟨z,hz,rfl⟩,?_⟩
    have hzI : z ∈ closure I := frontier_subset_closure (hIfr.symm ▸ hArcJ hz)
    exact mem_closure_image (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate_isOpenEmbedding P w).continuous.continuousAt hzI
  refine ⟨I,hIo,hIc,?_⟩
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichlet_Klein_strict_end_subset_region P w hw d.radius d.radius_pos
    (d.klein_originalArc_isPreconnected hw x) (d.klein_originalArc_subset_spherical_slice hw x)
    (d.klein_originalArc_isOpen_sphere hw x) hIo hIN hIfront hcontact


/-- Only finitely many genuine sides meet the actual closed radial end in the
finite-return case. This is proved from its genuine compact closure region and
the original locally finite side family, not from an assumed finite polygon. -/
theorem finite_period_radial_end_sides_finite
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hw :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hpos : 0 < d.endpointPeriod
      hw x) :
    {S | _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianPolygonSide P
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w) S ∧
      (S ∩ closure {z | z ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w ∧ d.radius <
        P.hyperbolicDist w z ∧
        _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection (Real.tanh
          d.radius) (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z) ∈
          _root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x}).Nonempty}.Finite := by
  obtain ⟨I,_hIo,hIc,hQI⟩ := d.finite_period_radial_end_precompact hNE hw x hpos
  apply ((_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain_locallyFinite P w hw).compact_sides_finite
    (closure I) hIc).subset
  rintro S ⟨hS,z,hzS,hzQ⟩
  exact ⟨hS,z,hzS,closure_mono hQI hzQ⟩

end RegularDirichletCircleData
end LowDimensionalTopology.Geometry.Fuchsian
