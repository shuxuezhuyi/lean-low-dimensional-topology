module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.CircleArcIncidence
@[expose] public section
noncomputable section
open Set
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian

/-- Reversing the actual arc conjugates the alternating endpoint motion to its inverse. -/
theorem alternatingArc_reversal_conjugation {X : Type*} (a b : Equiv.Perm X)
    (ha : Function.Involutive a) (hb : Function.Involutive b) (n : ℕ) (x : X) :
    ((a*b)^n) (b (((a*b)^n) x)) = b x := by
  have hrr (y : X) : (a*b) (b ((a*b) y)) = b y := by
    change a (b (b (a (b y)))) = b y
    rw [hb (a (b y)),ha (b y)]
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ((a*b)^(n+1)) (b (((a*b)^(n+1)) x)) =
            ((a*b)^n) ((a*b) (b ((a*b) (((a*b)^n) x)))) := by
              have hout (z : X) : ((a*b)^(n+1)) z = ((a*b)^n) ((a*b) z) := by
                rw [pow_succ,Equiv.Perm.mul_apply]
              have hin : ((a*b)^(n+1)) x = (a*b) (((a*b)^n) x) := by
                rw [pow_succ',Equiv.Perm.mul_apply]
              exact (hout _).trans (congrArg (fun z => ((a*b)^n) ((a*b) (b z))) hin)
        _ = ((a*b)^n) (b (((a*b)^n) x)) := by rw [hrr]
        _ = b x := ih

/-- For two genuine fixed-point-free involutions, the alternating endpoint motion
never returns to the opposite endpoint of the same original arc. -/
theorem alternatingArc_ne_reverse {X : Type*} (a b : Equiv.Perm X)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (haNe : ∀ x, a x ≠ x) (hbNe : ∀ x, b x ≠ x) (n : ℕ) :
    ∀ x : X, ((a*b)^n) x ≠ b x := by
  have hrr (y : X) : (a*b) (b ((a*b) y)) = b y := by
    change a (b (b (a (b y)))) = b y
    rw [hb (a (b y)),ha (b y)]
  induction n using Nat.twoStepInduction with
  | zero => intro x he; exact hbNe x he.symm
  | one =>
      intro x he
      have hh : a (b x) = b x := by simpa only [pow_one,Equiv.Perm.mul_apply] using he
      exact haNe (b x) hh
  | more n ih _ihnext =>
      intro x he
      apply ih ((a*b) x)
      apply (a*b).injective
      calc
        (a*b) (((a*b)^n) ((a*b) x)) = ((a*b)^(n+2)) x := by
          rw [←Equiv.Perm.mul_apply,←pow_succ',←Equiv.Perm.mul_apply,←pow_succ]
        _ = b x := he
        _ = (a*b) (b ((a*b) x)) := (hrr x).symm

/-- The two orientations of actual component arcs stay in disjoint alternating orbits. -/
theorem alternatingArc_pow_ne_reverse_pow {X : Type*} (a b : Equiv.Perm X)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (haNe : ∀ x, a x ≠ x) (hbNe : ∀ x, b x ≠ x) (m n : ℕ) (x : X) :
    ((a*b)^m) x ≠ b (((a*b)^n) x) := by
  intro he
  apply alternatingArc_ne_reverse a b ha hb haNe hbNe (n+m) x
  calc
    ((a*b)^(n+m)) x = ((a*b)^n) (((a*b)^m) x) := by rw [pow_add,Equiv.Perm.mul_apply]
    _ = ((a*b)^n) (b (((a*b)^n) x)) := congrArg ((a*b)^n) he
    _ = b x := alternatingArc_reversal_conjugation a b ha hb n x

/-- If every actual frontier point is incident to one actual open component, then
intersecting closures of actual components must be closures of the same component. -/
theorem component_closure_intersection_eq_of_unique_incidence
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    (hinc : ∀ p ∈ frontier U, ∃! V : Set X,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V)
    {V W : Set X} (hV : V ∈ ((fun x => connectedComponentIn U x) '' U))
    (hW : W ∈ ((fun x => connectedComponentIn U x) '' U))
    {p : X} (hpV : p ∈ closure V) (hpW : p ∈ closure W) : V = W := by
  by_cases hp : p ∈ U
  · obtain ⟨x,hx,rfl⟩ := hV
    obtain ⟨y,hy,rfl⟩ := hW
    have hv := closure_connectedComponentIn_inter_subset hx ⟨hpV,hp⟩
    have hw := closure_connectedComponentIn_inter_subset hy ⟨hpW,hp⟩
    exact (connectedComponentIn_eq hv).trans (connectedComponentIn_eq hw).symm
  · have hpf : p ∈ frontier U := by
      refine ⟨?_,?_⟩
      · obtain ⟨x,_hx,rfl⟩ := hV
        exact closure_mono (connectedComponentIn_subset U x) hpV
      · rwa [hU.interior_eq]
    obtain ⟨Q,_hQ,hunique⟩ := hinc p hpf
    exact (hunique V ⟨hV,hpV⟩).trans (hunique W ⟨hW,hpW⟩).symm

/-- Distinct actual component arcs have disjoint genuine compact closures when
actual endpoint incidence is unique. -/
theorem component_closures_disjoint_of_unique_incidence
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    (hinc : ∀ p ∈ frontier U, ∃! V : Set X,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V)
    {V W : Set X} (hV : V ∈ ((fun x => connectedComponentIn U x) '' U))
    (hW : W ∈ ((fun x => connectedComponentIn U x) '' U)) (hne : V ≠ W) :
    Disjoint (closure V) (closure W) := by
  apply disjoint_left.mpr
  intro p hpV hpW
  exact hne (component_closure_intersection_eq_of_unique_incidence hU hinc hV hW hpV hpW)

open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Equality of points in translated original polygon interiors forces equality
of the actual translating group elements as well as equality of original points. -/
theorem fuchsian_polygon_interior_translate_unique
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D)
    {v z : P.domain.carrier} (hv : v ∈ D) (hz : z ∈ D) (g h : H)
    (he : g • v = h • z) : g = h ∧ v = z := by
  have hred : (h⁻¹*g) • v = z := by rw [mul_smul,he,inv_smul_smul]
  have hunit : h⁻¹*g = 1 := by
    by_contra hne
    exact disjoint_left.mp (hD.disjoint_image_closure hne) ⟨v,hv,hred⟩ (subset_closure hz)
  have hgh : g = h := (inv_mul_eq_one.mp hunit).symm
  refine ⟨hgh,?_⟩
  rw [hunit,one_smul] at hred
  exact hred

/-- Distinct original open component arcs have disjoint interiors under arbitrary
actual group translations, including when the translating elements coincide. -/
theorem fuchsian_polygon_translated_subsets_disjoint
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D)
    {V W : Set P.domain.carrier} (hV : V ⊆ D) (hW : W ⊆ D)
    (hVW : Disjoint V W) (g h : H) : Disjoint (g • V) (h • W) := by
  apply disjoint_left.mpr
  rintro p ⟨v,hv,hgv⟩ ⟨z,hz,hgz⟩
  have he : g • v = h • z := hgv.trans hgz.symm
  have hvz := (fuchsian_polygon_interior_translate_unique hD (hV hv) (hW hz) g h he).2
  exact disjoint_left.mp hVW hv (hvz.symm ▸ hz)

/-- Any coincidence between actual translated cut endpoints comes either from the
same original endpoint or from its unique genuine Dirichlet pairing mate. -/
theorem dirichlet_circle_translated_cut_coincidence
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (x y : dirichletCircleCuts P w R) (g h : H) (he : g • x.val = h • y.val) :
    (g = h ∧ x = y) ∨
      (h⁻¹*g = dirichletCircleMateElement P w hw R hReg x ∧
        y = dirichletCircleCutPairing P w hw R hReg x) := by
  have hred : (h⁻¹*g) • x.val = y.val := by rw [mul_smul,he,inv_smul_smul]
  by_cases hunit : h⁻¹*g = 1
  · left
    refine ⟨(inv_mul_eq_one.mp hunit).symm,Subtype.ext ?_⟩
    simpa only [hunit,one_smul] using hred
  · right
    have hmem : (h⁻¹*g) • x.val ∈ dirichletCircleCuts P w R := hred.symm ▸ y.property
    have ht : h⁻¹*g = dirichletCircleMateElement P w hw R hReg x :=
      (dirichletCircleCut_mate_existsUnique P w hw R x.property (hReg x.val x.property)).choose_spec.2
        (h⁻¹*g) ⟨hunit,hmem⟩
    refine ⟨ht,Subtype.ext ?_⟩
    change y.val = dirichletCircleMateElement P w hw R hReg x • x.val
    rw [←ht,hred]

/-- Different alternating endpoint positions before a return cannot represent
the same genuine compact arc, even with reversed orientation. -/
theorem alternatingArc_component_ne_of_endpoint_ne
    {X Y : Type*} [TopologicalSpace Y] (a b : Equiv.Perm X)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (haNe : ∀ x, a x ≠ x) (hbNe : ∀ x, b x ≠ x)
    (v : X → Y) (hv : Function.Injective v) (C : X → Set Y)
    (hC : ∀ x, closure (C x) \ C x = {v x,v (b x)})
    (m n : ℕ) (x : X) (hne : ((a*b)^m) x ≠ ((a*b)^n) x) :
    C (((a*b)^m) x) ≠ C (((a*b)^n) x) := by
  intro he
  have hp : ({v (((a*b)^m) x),v (b (((a*b)^m) x))} : Set Y) =
      {v (((a*b)^n) x),v (b (((a*b)^n) x))} := by
    rw [←hC,←hC,he]
  rcases pair_eq_pair_iff.mp hp with ⟨hp,_hq⟩ | ⟨hp,_hq⟩
  · exact hne (hv hp)
  · exact alternatingArc_pow_ne_reverse_pow a b ha hb haNe hbNe m n x (hv hp)

/-- In the genuine circle, distinct positions of an alternating endpoint cycle
have genuinely disjoint compact component arcs when actual incidence is unique. -/
theorem alternatingArc_component_closures_disjoint
    {U : Set Circle} (hU : IsOpen U)
    (hinc : ∀ p ∈ frontier U, ∃! V : Set Circle,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V)
    {X : Type*} (E : ↥(frontier U) ≃ X) (a b : Equiv.Perm X)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (haNe : ∀ x, a x ≠ x) (hbNe : ∀ x, b x ≠ x)
    (C : X → Set Circle)
    (hComp : ∀ x, C x ∈ ((fun y => connectedComponentIn U y) '' U))
    (hEnds : ∀ x, closure (C x) \ C x = {(E.symm x).val,(E.symm (b x)).val})
    (m n : ℕ) (x : X) (hne : ((a*b)^m) x ≠ ((a*b)^n) x) :
    Disjoint (closure (C (((a*b)^m) x))) (closure (C (((a*b)^n) x))) := by
  apply component_closures_disjoint_of_unique_incidence hU hinc (hComp _) (hComp _)
  exact alternatingArc_component_ne_of_endpoint_ne a b ha hb haNe hbNe
    (fun z => (E.symm z).val) (Subtype.val_injective.comp E.symm.injective) C hEnds m n x hne

/-- The same alternating orbit also avoids the opposite actual pairing endpoint. -/
theorem alternatingArc_ne_pairing {X : Type*} (a b : Equiv.Perm X)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (haNe : ∀ x, a x ≠ x) (hbNe : ∀ x, b x ≠ x) (n : ℕ) (x : X) :
    ((a*b)^n) x ≠ a x := by
  intro he
  have hleft : Function.LeftInverse (b*a) (a*b) := by
    intro y
    change b (a (a (b y))) = y
    rw [ha (b y),hb y]
  have hi : ((b*a)^n) (((a*b)^n) x) = x := by
    simpa only [Equiv.Perm.coe_pow] using hleft.iterate n x
  apply alternatingArc_ne_reverse b a hb ha hbNe haNe n (((a*b)^n) x)
  rw [hi,he,ha x]

/-- Actual group-pairing mates, like arc reversals, lie in the other alternating orbit. -/
theorem alternatingArc_pow_ne_pairing_pow {X : Type*} (a b : Equiv.Perm X)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (haNe : ∀ x, a x ≠ x) (hbNe : ∀ x, b x ≠ x) (m n : ℕ) (x : X) :
    ((a*b)^m) x ≠ a (((a*b)^n) x) := by
  cases n with
  | zero => simpa only [pow_zero,Equiv.Perm.one_apply] using alternatingArc_ne_pairing a b ha hb haNe hbNe m x
  | succ n =>
      intro he
      apply alternatingArc_pow_ne_reverse_pow a b ha hb haNe hbNe m n x
      have hh : a (((a*b)^(n+1)) x) = b (((a*b)^n) x) := by
        rw [pow_succ',Equiv.Perm.mul_apply]
        change a (a (b (((a*b)^n) x))) = b (((a*b)^n) x)
        exact ha _
      exact he.trans hh

/-- Along an actual alternating Dirichlet endpoint orbit, coincidence of translated
starting vertices forces equality of both the actual tile and the original endpoint.
The other possible original pairing mate is excluded by the true fixed-free involutions. -/
theorem dirichlet_alternating_translated_starts_unique
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (a b : Equiv.Perm (dirichletCircleCuts P w R))
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (haNe : ∀ x, a x ≠ x) (hbNe : ∀ x, b x ≠ x)
    (hA : a = dirichletCircleCutPairing P w hw R hReg)
    (m n : ℕ) (x : dirichletCircleCuts P w R) (g h : H)
    (he : g • (((a*b)^m) x).val = h • (((a*b)^n) x).val) :
    g = h ∧ ((a*b)^m) x = ((a*b)^n) x := by
  rcases dirichlet_circle_translated_cut_coincidence P w hw R hReg
      (((a*b)^m) x) (((a*b)^n) x) g h he with hh | ⟨_hk,hh⟩
  · exact hh
  · have hn : ((a*b)^n) x = a (((a*b)^m) x) := by simpa only [hA] using hh
    exact False.elim (alternatingArc_pow_ne_pairing_pow a b ha hb haNe hbNe n m x hn)

end LowDimensionalTopology.Geometry.Fuchsian
