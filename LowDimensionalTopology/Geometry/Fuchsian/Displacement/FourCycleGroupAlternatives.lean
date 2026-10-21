/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.WeakDisplacementGap
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletCyclicOrder
@[expose] public section
noncomputable section
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Conjugation by the first involution preserves the subgroup generated
by its two actual even products. -/
theorem even_involution_pair_conjugate_mem (f g h : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f*f=1) (hg : g*g=1) (hh : h*h=1)
    (k : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hk : k∈Subgroup.closure ({f*g,f*h}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) :
    f*k*f∈Subgroup.closure ({f*g,f*h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  let K:=Subgroup.closure ({f*g,f*h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hfi : f⁻¹=f:=inv_eq_of_mul_eq_one_left hf
  have hgi : g⁻¹=g:=inv_eq_of_mul_eq_one_left hg
  have hhi : h⁻¹=h:=inv_eq_of_mul_eq_one_left hh
  have hle : K.map (MulAut.conj f).toMonoidHom≤K:=by
    rw [MonoidHom.map_closure,Set.image_pair]
    apply (Subgroup.closure_le _).mpr
    intro u hu
    rcases hu with rfl|rfl
    · have he : (MulAut.conj f) (f*g)=(f*g)⁻¹:=by
        change f*(f*g)*f⁻¹=(f*g)⁻¹
        rw [hfi,mul_inv_rev,hgi,hfi]
        calc
          f*(f*g)*f=(f*f)*(g*f):=by group
          _=g*f:=by rw [hf,one_mul]
      change (MulAut.conj f) _∈K
      rw [he]
      exact K.inv_mem (Subgroup.subset_closure (by simp))
    · have he : (MulAut.conj f) (f*h)=(f*h)⁻¹:=by
        change f*(f*h)*f⁻¹=(f*h)⁻¹
        rw [hfi,mul_inv_rev,hhi,hfi]
        calc
          f*(f*h)*f=(f*f)*(h*f):=by group
          _=h*f:=by rw [hf,one_mul]
      change (MulAut.conj f) _∈K
      rw [he]
      exact K.inv_mem (Subgroup.subset_closure (by simp))
  have hm : (MulAut.conj f) k∈K.map (MulAut.conj f).toMonoidHom:=⟨k,hk,rfl⟩
  have hout:=hle hm
  change f*k*f⁻¹∈K at hout
  rwa [hfi] at hout

/-- The actual three-involution group is contained in the two cosets of
its true even-product subgroup. No parity homomorphism is assumed. -/
theorem triple_involution_even_pair_cosets (f g h : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f*f=1) (hg : g*g=1) (hh : h*h=1)
    (u : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hu : u∈Subgroup.closure ({f,g,h}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) :
    u∈Subgroup.closure ({f*g,f*h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) ∨
      ∃k∈Subgroup.closure ({f*g,f*h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup),u=f*k := by
  let K:=Subgroup.closure ({f*g,f*h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hfi : f⁻¹=f:=inv_eq_of_mul_eq_one_left hf
  have hn:=even_involution_pair_conjugate_mem f g h hf hg hh
  let S : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:={
    carrier:={a | a∈K ∨∃k∈K,a=f*k}
    one_mem':=Or.inl K.one_mem
    mul_mem':=by
      intro a b ha hb
      rcases ha with ha|⟨k,hk,rfl⟩ <;> rcases hb with hb|⟨l,hl,rfl⟩
      · exact Or.inl (K.mul_mem ha hb)
      · refine Or.inr ⟨(f*a*f)*l,K.mul_mem (hn a ha) hl,?_⟩
        calc
          a*(f*l)=(f*f)*a*f*l:=by simp only [hf,one_mul,mul_assoc]
          _=f*((f*a*f)*l):=by group
      · exact Or.inr ⟨k*b,K.mul_mem hk hb,by group⟩
      · left
        have he : (f*k)*(f*l)=(f*k*f)*l:=by group
        rw [he]
        exact K.mul_mem (hn k hk) hl
    inv_mem':=by
      intro a ha
      rcases ha with ha|⟨k,hk,rfl⟩
      · exact Or.inl (K.inv_mem ha)
      · refine Or.inr ⟨f*k⁻¹*f,hn _ (K.inv_mem hk),?_⟩
        rw [mul_inv_rev,hfi]
        calc
          k⁻¹*f=(f*f)*k⁻¹*f:=by rw [hf,one_mul]
          _=f*(f*k⁻¹*f):=by group }
  have hle : Subgroup.closure ({f,g,h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)≤S:=by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    rcases ha with rfl|rfl|rfl
    · exact Or.inr ⟨1,K.one_mem,by rw [mul_one]⟩
    · refine Or.inr ⟨f*a,Subgroup.subset_closure (by simp),?_⟩
      calc
        a=(f*f)*a:=by rw [hf,one_mul]
        _=f*(f*a):=by group
    · refine Or.inr ⟨f*a,Subgroup.subset_closure (by simp),?_⟩
      calc
        a=(f*f)*a:=by rw [hf,one_mul]
        _=f*(f*a):=by group
  exact hle hu

/-- If the actual even-product subgroup has a finite point orbit, the
three-involution group has a finite orbit in the same genuine model. -/
theorem triple_involution_elementary_of_even_pair (f g h :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f*f=1) (hg : g*g=1) (hh : h*h=1)
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f*g,f*h}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f,g,h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let K:=Subgroup.closure ({f*g,f*h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  obtain ⟨x,hx⟩:=he
  have hfinite : (MulAction.orbit K x ∪ (fun y :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.ClosedUpperHalfSpace=>f•y) '' MulAction.orbit K x).Finite:=
    hx.union (hx.image _)
  refine ⟨x,hfinite.subset ?_⟩
  rintro y ⟨u,rfl⟩
  rcases triple_involution_even_pair_cosets f g h hf hg hh u.val u.property with hu|⟨k,hk,heq⟩
  · exact Or.inl ⟨⟨u.val,hu⟩,rfl⟩
  · right
    refine ⟨k•x,⟨⟨k,hk⟩,rfl⟩,?_⟩
    change f•(k•x)=u.val•x
    rw [heq,mul_smul]

/-- The true even-product subgroup of a non-elementary three-involution
group is non-elementary, by the proved two-coset finite-orbit argument. -/
theorem triple_involution_even_pair_nonElementary (f g h :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f*f=1) (hg : g*g=1) (hh : h*h=1)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g,h}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f*g,f*h}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) :=
  fun he=>hne (triple_involution_elementary_of_even_pair f g h hf hg hh he)

theorem sinh_two_arsinh_thousandth_lt_hundredth :
    Real.sinh (2*Real.arsinh (1/1000:ℝ))<1/100 := by
  let t:=Real.arsinh (1/1000:ℝ)
  have hs : Real.sinh t=1/1000:=Real.sinh_arsinh _
  have hc:=Real.cosh_sq_sub_sinh_sq t
  rw [hs] at hc
  have hclt : Real.cosh t<2:=by nlinarith only [hc]
  rw [Real.sinh_two_mul,hs]
  linarith only [hclt]

/-- Every actual non-elementary triple of involutions has a positive
pointwise displacement gap, using its genuine even-product pair. -/
theorem radius_triple_involution_half_displacement_gap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g h : H)
    (hf : f.val*f.val=1) (hg : g.val*g.val=1) (hh : h.val*h.val=1)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({f.val,g.val,h.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (z : P.domain.carrier) :
    1/1000≤max (Real.sinh (P.hyperbolicDist z (f•z)/2))
      (max (Real.sinh (P.hyperbolicDist z (g•z)/2)) (Real.sinh (P.hyperbolicDist z (h•z)/2))) := by
  have hEven:=triple_involution_even_pair_nonElementary f.val g.val h.val hf hg hh hne
  have hgap:=radius_pair_half_displacement_gap P (f*g) (f*h) hEven z
  by_contra! hm
  have hF:=(le_max_left (Real.sinh (P.hyperbolicDist z (f•z)/2)) _).trans_lt hm
  have hG:=(le_max_of_le_right (le_max_left (Real.sinh (P.hyperbolicDist z (g•z)/2)) _)).trans_lt hm
  have hH:=(le_max_of_le_right (le_max_right _ (Real.sinh (P.hyperbolicDist z (h•z)/2)))).trans_lt hm
  have hdf : P.hyperbolicDist z (f•z)<2*Real.arsinh (1/1000:ℝ):=by
    have he:=Real.arsinh_strictMono hF
    rw [Real.arsinh_sinh] at he
    linarith only [he]
  have hdfg (k : H) (hk : Real.sinh (P.hyperbolicDist z (k•z)/2)<1/1000) :
      Real.sinh (P.hyperbolicDist z ((f*k)•z)/2)<1/100:=by
    have hdk : P.hyperbolicDist z (k•z)<2*Real.arsinh (1/1000:ℝ):=by
      have he:=Real.arsinh_strictMono hk
      rw [Real.arsinh_sinh] at he
      linarith only [he]
    have hd : P.hyperbolicDist z ((f*k)•z)/2<2*Real.arsinh (1/1000:ℝ):=by
      linarith only [radius_product_displacement_le P f k z,hdf,hdk]
    exact (Real.sinh_strictMono hd).trans sinh_two_arsinh_thousandth_lt_hundredth
  exact (not_lt_of_ge hgap) (max_lt (hdfg g hG) (hdfg h hH))

/-- The four genuine orbit points of a non-elementary involution triple
force a universal positive circle radius. -/
theorem radius_triple_involution_circle_gap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g h : H)
    (hf : f.val*f.val=1) (hg : g.val*g.val=1) (hh : h.val*h.val=1)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({f.val,g.val,h.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (w z : P.domain.carrier) (r : ℝ)
    (hz : P.hyperbolicDist w z=r) (hfd : P.hyperbolicDist w (f•z)=r)
    (hgd : P.hyperbolicDist w (g•z)=r) (hhd : P.hyperbolicDist w (h•z)=r) :
    1/1000≤Real.sinh r := by
  have hgap:=radius_triple_involution_half_displacement_gap P f g h hf hg hh hne z
  have hle (k : H) (hk : P.hyperbolicDist w (k•z)=r) :
      Real.sinh (P.hyperbolicDist z (k•z)/2)≤Real.sinh r:=by
    have ht:=P.hyperbolicDist_triangle z w (k•z)
    rw [P.hyperbolicDist_comm z w,hz,hk] at ht
    exact Real.sinh_le_sinh.mpr (by linarith only [ht])
  exact hgap.trans (max_le (hle f hfd) (max_le (hle g hgd) (hle h hhd)))


/-- Every elementary Fuchsian group preserves the actual finite boundary
fixed set of each of its nonidentity noninvolutory members. -/
theorem elementary_noninvolution_fixedSet_preserved {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (f g : H)
    (hf : f.val≠1) (hfs : f.val*f.val≠1) :
    g.val.val '' _root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints f.val=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints f.val := by
  rcases D.elementary_classification he with hcyc|⟨u,d,_,_,hmodel⟩
  · let cyclicElementaryGroup : IsCyclic H:=hcyc
    obtain ⟨a,ha⟩:=exists_zpow_surjective H
    obtain ⟨m,hm⟩:=ha g
    obtain ⟨n,hn⟩:=ha f
    have hcommSub : g*f=f*g:=by rw [←hm,←hn];exact zpow_mul_comm a m n
    have hcomm : g.val*f.val=f.val*g.val:=congrArg Subtype.val hcommSub
    have heq : g.val*f.val*g.val⁻¹=f.val:=by
      rw [hcomm,mul_assoc,mul_inv_cancel,mul_one]
    apply _root_.LowDimensionalTopology.Geometry.Mobius.mobiusIteration_preserves_of_conjugate_fixes f.val g.val hf
    intro z hz
    rw [heq]
    exact hz
  · have hpair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer:=by
      rw [hmodel]
      apply (Subgroup.closure_le _).mpr
      intro k hk
      rcases hk with rfl|rfl
      · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mem_zeroInftyPairStabilizer d
      · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer.mul_mem
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mem_zeroInftyPairStabilizer (-1))
          _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_mem_zeroInftyPairStabilizer
    let F:=u*f.val*u⁻¹
    let G:=u*g.val*u⁻¹
    have hFm : F∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H:=⟨f.val,f.property,rfl⟩
    have hGm : G∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H:=⟨g.val,g.property,rfl⟩
    have hFsq : F*F≠1:=by
      have hh:=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusIteration_conjugate_sq_ne_one f.val u (by simpa only [pow_two] using hfs)
      simpa only [pow_two] using hh
    have hFn : F≠1:=by intro hh;exact hFsq (by rw [hh,one_mul])
    have hfixed : F.val (0:ℂ)=(0:ℂ) ∧ F.val ∞=∞:=by
      rcases _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_zeroInftyPair_cases ⟨F,hpair
        hFm⟩ with hfix|hswap
      · exact hfix
      · exact (hFsq (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_endpoint_exchange_square F hswap.1
        hswap.2)).elim
    have hset : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints F={((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞}:=by
      ext z
      change F.val z=z ↔ z∈({((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using
        _root_.LowDimensionalTopology.Geometry.Mobius.mobius_boundary_fixed_iff_zero_infty F hFn hfixed.1 hfixed.2 z
    have hpres : G.val '' _root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints F=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints F:=by
      rw [hset]
      exact hpair hGm
    apply u.val.injective.image_injective
    rw [←_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,←_root_.LowDimensionalTopology.Geometry.Mobius.mobiusIteration_fixedPoints_conjugate f.val u]
    exact hpres

/-- A genuine three-generator group preserving one nonempty finite
boundary fixed set is elementary in the full original action. -/
theorem triple_elementary_of_preserved_fixedSet (f g h :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f≠1)
    (hg : g.val '' _root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints
      f=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints f)
    (hh : h.val '' _root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints
      f=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints f) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f,g,h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let S:=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints f
  have hself : f.val '' S=S:=by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩;change f.val (f.val a)=f.val a
      rw [show f.val a=a from ha];exact ha
    · intro hz;exact ⟨z,hz,hz⟩
  have hle : Subgroup.closure ({f,g,h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)≤_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer ⊤ S:=by
    apply (Subgroup.closure_le _).mpr
    intro k hk
    rcases hk with rfl|rfl|rfl
    · exact ⟨by trivial,hself⟩
    · exact ⟨by trivial,hg⟩
    · exact ⟨by trivial,hh⟩
  obtain ⟨z,hz⟩:=_root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_has_boundary_fixed f hf
  apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isElementary_iff_boundary_or_interior _).mpr
  left
  refine ⟨z,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_boundary_fixedPoints_finite f hf).subset ?_⟩
  rintro y ⟨k,rfl⟩
  have hpres:=(hle k.property).2
  change k.val.val z∈S
  rw [←hpres]
  exact Set.mem_image_of_mem k.val.val hz

/-- Pairwise elementarity around a chosen noninvolutory generator forces
the entire original triple to be elementary. -/
theorem radius_pairwiseElementary_noninvolution_triple_elementary
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (f g h
      : H)
    (hf : f.val≠1) (hfs : f.val*f.val≠1)
    (hfg : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hfh : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,h.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,g.val,h.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  have hp (k : H) (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure
    ({f.val,k.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
      k.val.val '' _root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints f.val=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints f.val:=by
    let K:=Subgroup.closure ({f.val,k.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    have hKH : K≤H:=(Subgroup.closure_le H).mpr
      (by intro a ha;rcases ha with rfl|rfl;exact f.property;exact k.property)
    exact elementary_noninvolution_fixedSet_preserved (radius_restrict P K hKH).asFuchsianDisc he
      ⟨f.val,Subgroup.subset_closure (by simp)⟩ ⟨k.val,Subgroup.subset_closure (by simp)⟩ hf hfs
  exact triple_elementary_of_preserved_fixedSet f.val g.val h.val hf (hp g hfg) (hp h hfh)


/-- A non-elementary original triple either has a non-elementary pair,
or all three original maps are involutions. This follows from the actual
Fuchsian classification, with no geometric orbit assumptions. -/
theorem radius_nonElementary_triple_pair_or_involutions {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g h : H)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({f.val,g.val,h.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∨
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,h.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∨
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({g.val,h.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∨
      (f.val*f.val=1 ∧ g.val*g.val=1 ∧ h.val*h.val=1) := by
  by_cases hfg : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,g.val}:Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))
  swap
  · exact Or.inl hfg
  by_cases hfh : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,h.val}:Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))
  swap
  · exact Or.inr (Or.inl hfh)
  by_cases hgh : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({g.val,h.val}:Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))
  swap
  · exact Or.inr (Or.inr (Or.inl hgh))
  right;right;right
  refine ⟨?_,?_,?_⟩
  · by_contra hfs
    have hf1 : f.val≠1:=by intro he;apply hfs;rw [he,one_mul]
    exact hne (radius_pairwiseElementary_noninvolution_triple_elementary P f g h hf1 hfs hfg hfh)
  · by_contra hgs
    have hg1 : g.val≠1:=by intro he;apply hgs;rw [he,one_mul]
    have hgf : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({g.val,f.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
      rwa [Set.pair_comm]
    have he:=radius_pairwiseElementary_noninvolution_triple_elementary P g f h hg1 hgs hgf hgh
    rw [Set.insert_comm g.val f.val] at he
    exact hne he
  · by_contra hhs
    have hh1 : h.val≠1:=by intro he;apply hhs;rw [he,one_mul]
    have hhf : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({h.val,f.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
      rwa [Set.pair_comm]
    have hhg : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({h.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
      rwa [Set.pair_comm]
    have he:=radius_pairwiseElementary_noninvolution_triple_elementary P h f g hh1 hhs hhf hhg
    rw [Set.insert_comm h.val f.val,Set.pair_comm h.val g.val] at he
    exact hne he

/-- Every actual non-elementary original Fuchsian triple has a universal
positive pointwise displacement gap, including all elliptic cases. -/
theorem radius_nonElementary_triple_half_displacement_gap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g h : H)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({f.val,g.val,h.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (z : P.domain.carrier) :
    1/1000≤max (Real.sinh (P.hyperbolicDist z (f•z)/2))
      (max (Real.sinh (P.hyperbolicDist z (g•z)/2)) (Real.sinh (P.hyperbolicDist z (h•z)/2))) := by
  let F:=Real.sinh (P.hyperbolicDist z (f•z)/2)
  let G:=Real.sinh (P.hyperbolicDist z (g•z)/2)
  let J:=Real.sinh (P.hyperbolicDist z (h•z)/2)
  change 1/1000≤max F (max G J)
  rcases radius_nonElementary_triple_pair_or_involutions P f g h hne with he|he|he|⟨hf,hg,hh⟩
  · have hb:=radius_pair_half_displacement_gap P f g he z
    change 1/100≤max F G at hb
    have hm : max F G≤max F (max G J):=max_le (le_max_left _ _)
      ((le_max_left G J).trans (le_max_right F _))
    linarith only [hb,hm]
  · have hb:=radius_pair_half_displacement_gap P f h he z
    change 1/100≤max F J at hb
    have hm : max F J≤max F (max G J):=max_le (le_max_left _ _)
      ((le_max_right G J).trans (le_max_right F _))
    linarith only [hb,hm]
  · have hb:=radius_pair_half_displacement_gap P g h he z
    change 1/100≤max G J at hb
    have hm : max G J≤max F (max G J):=le_max_right _ _
    linarith only [hb,hm]
  · exact radius_triple_involution_half_displacement_gap P f g h hf hg hh hne z

/-- Four genuine original orbit points from a non-elementary triple have
a universal positive metric-circle radius, without an elementary-pair hypothesis. -/
theorem radius_nonElementary_triple_circle_gap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g h : H)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({f.val,g.val,h.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (w z : P.domain.carrier) (r : ℝ)
    (hz : P.hyperbolicDist w z=r) (hfd : P.hyperbolicDist w (f•z)=r)
    (hgd : P.hyperbolicDist w (g•z)=r) (hhd : P.hyperbolicDist w (h•z)=r) :
    1/1000≤Real.sinh r := by
  have hgap:=radius_nonElementary_triple_half_displacement_gap P f g h hne z
  have hle (k : H) (hk : P.hyperbolicDist w (k•z)=r) :
      Real.sinh (P.hyperbolicDist z (k•z)/2)≤Real.sinh r:=by
    have ht:=P.hyperbolicDist_triangle z w (k•z)
    rw [P.hyperbolicDist_comm z w,hz,hk] at ht
    exact Real.sinh_le_sinh.mpr (by linarith only [ht])
  exact hgap.trans (max_le (hle f hfd) (max_le (hle g hgd) (hle h hhd)))

theorem radius_nonElementary_triple_circle_cosh_gap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g h : H)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({f.val,g.val,h.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (w z : P.domain.carrier) (r : ℝ)
    (hz : P.hyperbolicDist w z=r) (hfd : P.hyperbolicDist w (f•z)=r)
    (hgd : P.hyperbolicDist w (g•z)=r) (hhd : P.hyperbolicDist w (h•z)=r) :
    Real.sqrt (1000001/1000000:ℝ)≤Real.cosh r := by
  have hs:=radius_nonElementary_triple_circle_gap P f g h hne w z r hz hfd hgd hhd
  apply Real.sqrt_le_iff.mpr
  refine ⟨(Real.cosh_pos r).le,?_⟩
  nlinarith [Real.cosh_sq_sub_sinh_sq r]

/-- Literal cycle length four supplies four actual distinct original
points, their true common metric radius, and their nearest-orbit property. -/
theorem dirichlet_four_cycle_points {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (hn : fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x)=4) :
    ∃p : Fin 4→P.domain.carrier, Function.Injective p ∧
      Set.range p=fuchsianPolygonCycle P (dirichletDomain P w) x ∧
      (∀i,P.hyperbolicDist w (p i)=P.hyperbolicDist w x) ∧
      (∀i,∀k : H,P.hyperbolicDist w (p i)≤P.hyperbolicDist w (k•p i)) := by
  classical
  obtain ⟨s,hs,e,_⟩:=dirichlet_cycle_argument_order P w hw x hx
  have hcard : s.card=4:=by
    unfold fuchsianPolygonCycleLength at hn
    rw [←hs] at hn
    simpa only [Set.ncard_coe_finset] using hn
  let e4 : Fin 4≃s:=(finCongr hcard).symm.trans e
  let p : Fin 4→P.domain.carrier:=fun i=>(e4 i).val
  have hp : Function.Injective p:=fun i j he=>e4.injective (Subtype.ext he)
  have hpr : Set.range p=fuchsianPolygonCycle P (dirichletDomain P w) x:=by
    rw [←hs]
    ext y
    constructor
    · rintro ⟨i,rfl⟩;exact (e4 i).property
    · intro hy;exact ⟨e4.symm ⟨y,hy⟩,congrArg Subtype.val (e4.apply_symm_apply ⟨y,hy⟩)⟩
  have hpi (i : Fin 4) : p i∈fuchsianPolygonCycle P (dirichletDomain P w) x:=by
    rw [←hpr];exact Set.mem_range_self i
  have hP:=dirichletDomain_isConvexFuchsianPolygon P w hw
  have hxc : x∈fuchsianPolygonCycle P (dirichletDomain P w) x:=
    ⟨(hx.mem_frontier hP.locallyFinite.fundamental).1,⟨1,one_smul _ _⟩⟩
  refine ⟨p,hp,hpr,?_,?_⟩
  · intro i
    have he:=dirichlet_cycle_distance_to_center_eq P w x (hpi i) hxc
    rw [P.hyperbolicDist_comm w (p i),P.hyperbolicDist_comm w x]
    exact he
  · intro i k
    have ht:=closure_dirichletDomain_le P w (hpi i).1 k⁻¹
    rw [P.hyperbolicDist_inverse_smul,inv_inv,P.hyperbolicDist_comm (p i) w,
      P.hyperbolicDist_comm (k•p i) w] at ht
    exact ht

end LowDimensionalTopology.Geometry.Fuchsian
