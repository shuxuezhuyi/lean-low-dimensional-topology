/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.HandleModels
public import Mathlib.Analysis.SpecialFunctions.Sqrt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology Metric
namespace LowDimensionalTopology.Geometry.Surfaces

/-- Two literal closed discs, glued pointwise exactly along their actual boundary circle. -/
def closedDiscDoubleSetoid : Setoid (Bool×Metric.closedBall (0:ℂ) 1) where
  r a b:=a.2=b.2 ∧ (a.1=b.1 ∨ ‖a.2.val‖=1)
  iseqv:=⟨fun a=>⟨rfl,Or.inl rfl⟩,by
    intro a b h
    exact ⟨h.1.symm,h.2.elim (fun he=>Or.inl he.symm) (fun hn=>Or.inr (h.1 ▸ hn))⟩,by
    intro a b c hab hbc
    refine ⟨hab.1.trans hbc.1,?_⟩
    rcases hab.2 with he|hn
    · rcases hbc.2 with he'|hn'
      · exact Or.inl (he.trans he')
      · exact Or.inr (hab.1.symm ▸ hn')
    · exact Or.inr hn⟩

def ClosedDiscDouble:=Quotient closedDiscDoubleSetoid

instance closedDiscDoubleTopology : TopologicalSpace ClosedDiscDouble:=
  inferInstanceAs (TopologicalSpace (Quotient closedDiscDoubleSetoid))

/-- The actual two hemisphere parametrizations in genuine Euclidean three-space. -/
def closedDiscHemisphereVector (p : Bool×Metric.closedBall (0:ℂ) 1) : EuclideanSpace ℝ (Fin 3):=
  WithLp.toLp 2 ![p.2.val.re,p.2.val.im,
    if p.1 then Real.sqrt (1-Complex.normSq p.2.val) else -Real.sqrt (1-Complex.normSq p.2.val)]

theorem closedDiscHemisphereVector_norm (p : Bool×Metric.closedBall (0:ℂ) 1) :
    ‖closedDiscHemisphereVector p‖=1 := by
  have hp : ‖p.2.val‖≤1:=by simpa only [mem_closedBall_zero_iff] using p.2.property
  have hN : 0≤1-Complex.normSq p.2.val:=by rw [Complex.normSq_eq_norm_sq];nlinarith [norm_nonneg p.2.val]
  have hs:=Real.sq_sqrt hN
  have he : ‖closedDiscHemisphereVector p‖^2=1:=by
    rw [EuclideanSpace.real_norm_sq_eq]
    cases p.1 <;> simp [closedDiscHemisphereVector,Fin.sum_univ_succ,Complex.normSq_apply] at * <;> nlinarith
  nlinarith [norm_nonneg (closedDiscHemisphereVector p)]

def closedDiscHemisphere (p : Bool×Metric.closedBall (0:ℂ) 1) :
    Metric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1:=
  ⟨closedDiscHemisphereVector p,by simpa only [mem_sphere_zero_iff_norm] using closedDiscHemisphereVector_norm p⟩

theorem closedDiscHemisphere_continuous : Continuous closedDiscHemisphere := by
  apply Continuous.subtype_mk
  apply continuous_prod_of_discrete_left.mpr
  intro b
  change Continuous (fun z : Metric.closedBall (0:ℂ) 1=>WithLp.toLp 2
    ![z.val.re,z.val.im,if b then Real.sqrt (1-Complex.normSq z.val) else -Real.sqrt (1-Complex.normSq z.val)])
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3=>ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> cases b <;> dsimp <;> fun_prop

/-- Equality in the actual sphere occurs precisely at the prescribed boundary gluing. -/
theorem closedDiscHemisphere_eq_iff (p q : Bool×Metric.closedBall (0:ℂ) 1) :
    closedDiscHemisphere p=closedDiscHemisphere q ↔ closedDiscDoubleSetoid p q := by
  constructor
  · intro h
    have hv:=congrArg Subtype.val h
    have h0:=congrArg (fun v:EuclideanSpace ℝ (Fin 3)=>v 0) hv
    have h1:=congrArg (fun v:EuclideanSpace ℝ (Fin 3)=>v 1) hv
    have h2:=congrArg (fun v:EuclideanSpace ℝ (Fin 3)=>v 2) hv
    have hz : p.2=q.2:=by
      apply Subtype.ext
      apply Complex.ext
      · exact h0
      · exact h1
    refine ⟨hz,?_⟩
    by_cases hb : p.1=q.1
    · exact Or.inl hb
    · right
      have hp : ‖p.2.val‖≤1:=by simpa only [mem_closedBall_zero_iff] using p.2.property
      have hN : 0≤1-Complex.normSq p.2.val:=by rw [Complex.normSq_eq_norm_sq];nlinarith [norm_nonneg p.2.val]
      have hs:=Real.sq_sqrt hN
      change (if p.1 then Real.sqrt (1-Complex.normSq p.2.val) else -Real.sqrt (1-Complex.normSq p.2.val))=
        (if q.1 then Real.sqrt (1-Complex.normSq q.2.val) else -Real.sqrt (1-Complex.normSq q.2.val)) at h2
      rw [←hz] at h2
      cases hpB:p.1 <;> cases hqB:q.1 <;> simp [hpB,hqB] at hb h2
      all_goals rw [Complex.normSq_eq_norm_sq] at hs h2; nlinarith [norm_nonneg p.2.val]
  · rintro ⟨hz,hb|hn⟩
    · have hpq : p=q:=Prod.ext hb hz
      rw [hpq]
    · apply Subtype.ext
      apply PiLp.ext
      intro i
      have hN : Complex.normSq p.2.val=1:=by rw [Complex.normSq_eq_norm_sq,hn];norm_num
      have hNq : Complex.normSq q.2.val=1:=hz ▸ hN
      fin_cases i <;> simp [closedDiscHemisphere,closedDiscHemisphereVector,hz,hNq]


/-- Every actual unit-sphere point is in one of the two genuine closed hemisphere images. -/
theorem closedDiscHemisphere_surjective : Function.Surjective closedDiscHemisphere := by
  intro v
  have hn : ‖v.val‖=1:=by simpa only [mem_sphere_zero_iff_norm] using v.property
  have hv : (v.val 0)^2+(v.val 1)^2+(v.val 2)^2=1:=by
    have hh:=EuclideanSpace.real_norm_sq_eq v.val
    rw [hn] at hh
    simpa [Fin.sum_univ_succ,add_assoc] using hh.symm
  let z:ℂ:=⟨v.val 0,v.val 1⟩
  have hzN : Complex.normSq z=(v.val 0)^2+(v.val 1)^2:=by simp [z,Complex.normSq_apply,pow_two]
  have hz : z∈Metric.closedBall (0:ℂ) 1:=by
    rw [mem_closedBall_zero_iff]
    have he : ‖z‖^2≤1:=by rw [←Complex.normSq_eq_norm_sq,hzN];nlinarith [sq_nonneg (v.val 2)]
    nlinarith [norm_nonneg z]
  let p:Metric.closedBall (0:ℂ) 1:=⟨z,hz⟩
  have hRad : 1-Complex.normSq p.val=(v.val 2)^2:=by change 1-Complex.normSq z=_;rw [hzN];linarith [hv]
  by_cases hp : 0≤v.val 2
  · refine ⟨(true,p),?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · rfl
    · rfl
    · change Real.sqrt (1-Complex.normSq p.val)=v.val 2
      rw [hRad,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]
  · refine ⟨(false,p),?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · rfl
    · rfl
    · change -Real.sqrt (1-Complex.normSq p.val)=v.val 2
      rw [hRad,Real.sqrt_sq_eq_abs,abs_of_nonpos (le_of_not_ge hp),neg_neg]

def closedDiscDoubleSphereMap : ClosedDiscDouble→Metric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1:=
  Quotient.lift closedDiscHemisphere (fun p q h=>(closedDiscHemisphere_eq_iff p q).mpr h)

theorem closedDiscDoubleSphereMap_continuous : Continuous closedDiscDoubleSphereMap:=
  continuous_quot_lift _ closedDiscHemisphere_continuous

theorem closedDiscDoubleSphereMap_bijective : Function.Bijective closedDiscDoubleSphereMap := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with
    | h p =>
      induction q using Quotient.inductionOn with
      | h q =>
        intro he
        exact Quotient.sound ((closedDiscHemisphere_eq_iff p q).mp he)
  · intro v
    obtain ⟨p,hp⟩:=closedDiscHemisphere_surjective v
    exact ⟨Quotient.mk closedDiscDoubleSetoid p,hp⟩

instance closedDiscDoubleCompact : CompactSpace ClosedDiscDouble:=
  inferInstanceAs (CompactSpace (Quotient closedDiscDoubleSetoid))

/-- The actual pointwise boundary double is the genuine topological two-sphere. -/
def closedDiscDoubleSphereHomeomorph : ClosedDiscDouble≃ₜMetric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1:=
  Continuous.homeoOfEquivCompactToT2
    (f:=Equiv.ofBijective closedDiscDoubleSphereMap closedDiscDoubleSphereMap_bijective)
    closedDiscDoubleSphereMap_continuous

/-- Actual genus zero is witnessed by the real sphere homeomorphism, not by an Euler expression. -/
theorem closedDiscDouble_hasTopologicalGenus_zero : HasTopologicalGenus ClosedDiscDouble 0 :=
  ⟨closedDiscDoubleSphereHomeomorph.trans canonicalHandleSurfaceZeroHomeomorph.symm⟩



/-- The actual two-copy boundary gluing for an arbitrary specified topological region. -/
def boundaryDoubleSetoid (X : Type*) (B : Set X) : Setoid (Bool×X) where
  r a b:=a.2=b.2 ∧ (a.1=b.1 ∨ a.2∈B)
  iseqv:=⟨fun a=>⟨rfl,Or.inl rfl⟩,by
    intro a b h
    exact ⟨h.1.symm,h.2.elim (fun he=>Or.inl he.symm) (fun hn=>Or.inr (h.1 ▸ hn))⟩,by
    intro a b c hab hbc
    refine ⟨hab.1.trans hbc.1,?_⟩
    rcases hab.2 with he|hn
    · rcases hbc.2 with he'|hn'
      · exact Or.inl (he.trans he')
      · exact Or.inr (hab.1.symm ▸ hn')
    · exact Or.inr hn⟩

def BoundaryDouble (X : Type*) (B : Set X):=Quotient (boundaryDoubleSetoid X B)

instance boundaryDoubleTopology (X : Type*) [TopologicalSpace X] (B : Set X) :
    TopologicalSpace (BoundaryDouble X B):=
  inferInstanceAs (TopologicalSpace (Quotient (boundaryDoubleSetoid X B)))

/-- An actual boundary-preserving homeomorphism descends to the genuine two-copy doubles. -/
def boundaryDoubleCongr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {B : Set X} {C : Set Y} (E : X≃ₜY) (hB : ∀x,x∈B↔E x∈C) :
    BoundaryDouble X B≃ₜBoundaryDouble Y C :=
  Homeomorph.Quotient.congr ((Homeomorph.refl Bool).prodCongr E) (by
    intro a b
    change (a.2=b.2 ∧ (a.1=b.1 ∨ a.2∈B)) ↔
      (E a.2=E b.2 ∧ (a.1=b.1 ∨ E a.2∈C))
    rw [E.injective.eq_iff,←hB])

def boundaryDoubleClosedDiscHomeomorph :
    BoundaryDouble (Metric.closedBall (0:ℂ) 1) {z|‖z.val‖=1}≃ₜClosedDiscDouble :=
  Homeomorph.Quotient.congrRight (fun _ _=>Iff.rfl)

/-- Every actual closed bounded convex planar region with nonempty interior has a boundary-preserving
genuine closed-disc model. -/
theorem closedConvexRegion_exists_discHomeomorph {S : Set ℂ}
    (hS : IsClosed S) (hconv : Convex ℝ S) (hne : (interior S).Nonempty) (hb : Bornology.IsBounded S) :
    ∃E:S≃ₜMetric.closedBall (0:ℂ) 1,∀p:S,p.val∈frontier S↔‖(E p).val‖=1 := by
  obtain ⟨h,hI,hCl,hF⟩:=exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hb
  have hImage : h '' S=Metric.closedBall (0:ℂ) 1:=by simpa only [hS.closure_eq] using hCl
  let E:S≃ₜMetric.closedBall (0:ℂ) 1:=(h.image S).trans (Homeomorph.setCongr hImage)
  refine ⟨E,?_⟩
  intro p
  change p.val∈frontier S ↔ ‖h p.val‖=1
  rw [←mem_sphere_zero_iff_norm,←hF,h.injective.mem_set_image]

/-- The actual boundary double of every genuine compact convex planar region is the actual sphere. -/
def closedConvexRegionDoubleSphereHomeomorph {S : Set ℂ}
    (hS : IsClosed S) (hconv : Convex ℝ S) (hne : (interior S).Nonempty) (hb : Bornology.IsBounded S) :
    BoundaryDouble S {p|p.val∈frontier S}≃ₜMetric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1 := by
  let hex:=closedConvexRegion_exists_discHomeomorph hS hconv hne hb
  let E:=hex.choose
  have hE:=hex.choose_spec
  exact (boundaryDoubleCongr E hE).trans
    (boundaryDoubleClosedDiscHomeomorph.trans closedDiscDoubleSphereHomeomorph)

theorem closedConvexRegionDouble_hasTopologicalGenus_zero {S : Set ℂ}
    (hS : IsClosed S) (hconv : Convex ℝ S) (hne : (interior S).Nonempty) (hb : Bornology.IsBounded S) :
    HasTopologicalGenus (BoundaryDouble S {p|p.val∈frontier S}) 0 :=
  ⟨(closedConvexRegionDoubleSphereHomeomorph hS hconv hne hb).trans canonicalHandleSurfaceZeroHomeomorph.symm⟩

end LowDimensionalTopology.Geometry.Surfaces
