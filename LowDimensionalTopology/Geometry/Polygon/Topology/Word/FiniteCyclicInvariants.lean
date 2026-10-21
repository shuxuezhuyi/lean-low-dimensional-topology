/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.FiniteCyclicNormalizationResult
@[expose] public section
noncomputable section
set_option autoImplicit false
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation
open SurfaceCellComplex
namespace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface

/-- Closedness is the genuine incidence condition: every stored edge occurs twice. -/
def IsClosed (P:FiniteCyclicPresentation) : Prop:=∀e:P.Edge,P.edgeMultiplicity e=2

theorem signedIso_closed_iff {P Q:FiniteCyclicPresentation} (e:SignedPresentationIso P Q) :
    IsClosed P↔IsClosed Q := by
  constructor
  · intro h b
    obtain ⟨a,rfl⟩:=e.edgeEquiv.surjective b
    rw [←e.edgeMultiplicity_eq]
    exact h a
  · intro h a
    rw [e.edgeMultiplicity_eq]
    exact h _

theorem unorientedIso_closed_iff {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q) :
    IsClosed P↔IsClosed Q := by
  constructor
  · intro h b
    obtain ⟨a,rfl⟩:=e.edgeEquiv.surjective b
    rw [←e.edgeMultiplicity_eq]
    exact h a
  · intro h a
    rw [e.edgeMultiplicity_eq]
    exact h _

theorem p1_closed_iff (P:FiniteCyclicPresentation) (a:P.Edge) :
    IsClosed P↔IsClosed (P1.expand P a) := by
  constructor
  · intro h e
    refine Fin.lastCases ?_ (fun b=>?_) e
    · change (P1.expand P a).edgeMultiplicity (P1.freshEdge P.edgeCount)=2
      rw [←P1.edgeMultiplicity_expand_freshEdge P a]
      exact h a
    · rw [←P1.edgeMultiplicity_expand_castSucc P a b]
      exact h b
  · intro h e
    rw [P1.edgeMultiplicity_expand_castSucc P a e]
    exact h _

theorem p2_closed_iff (P:FiniteCyclicPresentation) (cut:P2Cut P) :
    IsClosed P↔IsClosed (P2.split P cut) := by
  constructor
  · intro h e
    refine Fin.lastCases ?_ (fun b=>?_) e
    · exact P2.edgeMultiplicity_split_freshEdge P cut
    · rw [←P2.edgeMultiplicity_split_castSucc P cut b]
      exact h b
  · intro h e
    rw [P2.edgeMultiplicity_split_castSucc P cut e]
    exact h _

theorem p1Subdivision_closed_iff {P Q:FiniteCyclicPresentation} (h:P1Subdivision P Q) :
    IsClosed P↔IsClosed Q := by
  obtain ⟨a,⟨e⟩⟩:=h
  exact (p1_closed_iff P a).trans (signedIso_closed_iff e)

theorem p2Subdivision_closed_iff {P Q:FiniteCyclicPresentation} (h:P2Subdivision P Q) :
    IsClosed P↔IsClosed Q := by
  obtain ⟨cut,_,⟨e⟩⟩:=h
  exact (p2_closed_iff P cut).trans (signedIso_closed_iff e)

theorem subdivisionStep_closed_iff {P Q:FiniteCyclicPresentation} (h:SubdivisionStep P Q) :
    IsClosed P↔IsClosed Q := by
  rcases h with hi|h|h
  · obtain ⟨e⟩:=hi
    exact signedIso_closed_iff e
  · exact p1Subdivision_closed_iff h
  · exact p2Subdivision_closed_iff h

theorem subdivides_closed_iff {P Q:FiniteCyclicPresentation} (h:Subdivides P Q) :
    IsClosed P↔IsClosed Q := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hs ih => exact ih.trans (subdivisionStep_closed_iff hs)

theorem commonSubdivision_closed_iff {P Q:FiniteCyclicPresentation} (h:HasCommonSubdivision P Q) :
    IsClosed P↔IsClosed Q := by
  obtain ⟨R,hPR,hQR⟩:=h
  exact (subdivides_closed_iff hPR).trans (subdivides_closed_iff hQR).symm

theorem normalizationStep_closed_iff {P Q:ValidPresentation} (h:NormalizationStep P Q) :
    IsClosed P.presentation↔IsClosed Q.presentation := by
  cases h with
  | commonSubdivision h => exact commonSubdivision_closed_iff h
  | unoriented h =>
    rcases h with hf|hb
    · obtain ⟨e⟩:=hf
      exact unorientedIso_closed_iff e
    · obtain ⟨e⟩:=hb
      exact (unorientedIso_closed_iff e).symm
  | oneSidedP2 cut _ => exact p2_closed_iff _ cut

theorem normalizationEquivalent_closed_iff {P Q:ValidPresentation} (h:NormalizationEquivalent P Q) :
    IsClosed P.presentation↔IsClosed Q.presentation := by
  induction h with
  | rel _ _ h => exact normalizationStep_closed_iff h
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ij => exact ih.trans ij

theorem normalizationResult_closed_iff {P:ValidPresentation} (r:NormalizationResult P) :
    IsClosed P.presentation↔IsClosed r.normalForm.canonicalPresentation :=
  normalizationEquivalent_closed_iff r.equivalent

theorem oneFace_closed_iff {E:Type} [Fintype E] [DecidableEq E]
    (w:List (SignedDart E)) :
    IsClosed (ofOneFaceWord w)↔∀e:E,(w.map edgeOfDart).count e=2 := by
  constructor
  · intro h e
    rw [←ofOneFaceWord_edgeMultiplicity]
    exact h _
  · intro h e
    obtain ⟨a,rfl⟩:=(ofOneFaceWordEdgeEquiv w).surjective e
    rw [ofOneFaceWord_edgeMultiplicity]
    exact h a

theorem orientableCanonical_closed_iff (p b:ℕ) :
    IsClosed (NormalForm.orientable p b).canonicalPresentation↔b=0 := by
  rw [NormalForm.canonicalPresentation_orientable,oneFace_closed_iff]
  have hc (e:NormalForm.OrientableEdge p b) :
      ((NormalForm.orientableBoundaryWord p b).map edgeOfDart).count e=
        match e with | .a _=>2 | .b _=>2 | .c _=>2 | .h _=>1 :=by
    rw [map_edgeOfDart_eq_map_edgeName,←SurfaceCellComplex.wordEdgeOccurrences_card_eq_count_edgeName]
    exact NormalForm.orientableBoundaryWord_edge_occurrences p b e
  constructor
  · intro h
    by_contra hb
    have hi:0<b:=Nat.pos_of_ne_zero hb
    have hh:=h (NormalForm.OrientableEdge.h ⟨0,hi⟩)
    rw [hc] at hh
    norm_num at hh
  · rintro rfl e
    rw [hc]
    cases e with
    | a _ =>rfl
    | b _ =>rfl
    | c i =>exact Fin.elim0 i
    | h i =>exact Fin.elim0 i

theorem nonorientableCanonical_closed_iff (p b:ℕ) :
    IsClosed (NormalForm.nonOrientable p b).canonicalPresentation↔b=0 := by
  rw [NormalForm.canonicalPresentation_nonOrientable,oneFace_closed_iff]
  have hc (e:NormalForm.NonOrientableEdge p b) :
      ((NormalForm.nonOrientableBoundaryWord p b).map edgeOfDart).count e=
        match e with | .a _=>2 | .c _=>2 | .h _=>1 :=by
    rw [map_edgeOfDart_eq_map_edgeName,←SurfaceCellComplex.wordEdgeOccurrences_card_eq_count_edgeName]
    exact NormalForm.nonOrientableBoundaryWord_edge_occurrences p b e
  constructor
  · intro h
    by_contra hb
    have hi:0<b:=Nat.pos_of_ne_zero hb
    have hh:=h (NormalForm.NonOrientableEdge.h ⟨0,hi⟩)
    rw [hc] at hh
    norm_num at hh
  · rintro rfl e
    rw [hc]
    cases e with
    | a _ =>rfl
    | c i =>exact Fin.elim0 i
    | h i =>exact Fin.elim0 i

theorem sphereCanonical_closed :IsClosed NormalForm.sphere.canonicalPresentation:=by
  intro e
  exact twoMonogonSphere_edgeMultiplicity e

/-- A closed input cannot normalize to a canonical surface with any boundary component. -/
theorem closed_normalizationResult_boundary_zero {P:ValidPresentation} (r:NormalizationResult P)
    (h:IsClosed P.presentation) :
    r.normalForm=.sphere ∨
      (∃g,r.normalForm=.orientable g 0) ∨ (∃g,r.normalForm=.nonOrientable g 0) := by
  have hN: IsClosed r.normalForm.canonicalPresentation:=(normalizationResult_closed_iff r).mp h
  cases he:r.normalForm with
  | sphere =>exact Or.inl rfl
  | orientable g b =>
    have hb:b=0:=(orientableCanonical_closed_iff g b).mp (he ▸ hN)
    subst b
    exact Or.inr (Or.inl ⟨g,rfl⟩)
  | nonOrientable g b =>
    have hb:b=0:=(nonorientableCanonical_closed_iff g b).mp (he ▸ hN)
    subst b
    exact Or.inr (Or.inr ⟨g,rfl⟩)

/-- Signed incidence of an actual oriented occurrence at the specified edge. -/
def dartCoefficient {E:Type} [DecidableEq E] (e:E) :SignedDart E→ℤ
  | .pos a=>if a=e then 1 else 0
  | .neg a=>if a=e then -1 else 0

/-- The literal signed incidence of a stored finite boundary word. -/
def wordCoefficient {E:Type} [DecidableEq E] (e:E) (w:List (SignedDart E)) :ℤ:=
  (w.map (dartCoefficient e)).sum

@[simp] theorem wordCoefficient_nil {E:Type} [DecidableEq E] (e:E) :
    wordCoefficient e []=0:=rfl

@[simp] theorem wordCoefficient_cons {E:Type} [DecidableEq E] (e:E)
    (d:SignedDart E) (w:List (SignedDart E)) :
    wordCoefficient e (d::w)=dartCoefficient e d+wordCoefficient e w:=rfl

theorem wordCoefficient_append {E:Type} [DecidableEq E] (e:E)
    (u v:List (SignedDart E)) :
    wordCoefficient e (u++v)=wordCoefficient e u+wordCoefficient e v:=by
  simp only [wordCoefficient,List.map_append,List.sum_append]

theorem wordCoefficient_rotated {E:Type} [DecidableEq E] (e:E)
    {u v:List (SignedDart E)} (h:u.IsRotated v) :
    wordCoefficient e u=wordCoefficient e v:=
  (h.perm.map (dartCoefficient e)).sum_eq

theorem dartCoefficient_flip {E:Type} [DecidableEq E] (e:E) (d:SignedDart E) :
    dartCoefficient e d.flip= -dartCoefficient e d:=by
  cases d <;> simp only [SignedDart.flip,dartCoefficient] <;> split_ifs <;> norm_num

theorem wordCoefficient_inverse {E:Type} [DecidableEq E] (e:E) (w:List (SignedDart E)) :
    wordCoefficient e (inverseWord w)= -wordCoefficient e w:=by
  induction w with
  | nil=>simp only [inverseWord_nil,wordCoefficient_nil,neg_zero]
  | cons d w ih=>
    rw [show inverseWord (d::w)=inverseWord w++[d.flip] by simp [inverseWord],
      wordCoefficient_append,ih,wordCoefficient_cons,wordCoefficient_nil,dartCoefficient_flip,
      wordCoefficient_cons]
    ring

/-- Multiplication by this sign reverses an oriented face traversal. -/
def paritySign (b:Bool) :ℤ:=if b then -1 else 1

theorem paritySign_sq (b:Bool) :paritySign b*paritySign b=1:=by cases b <;> rfl

theorem paritySign_ne_zero (b:Bool) :paritySign b≠0:=by cases b <;> decide

theorem orientedBoundary_coefficient (P:FiniteCyclicPresentation) (f:P.OrientedFace) (e:P.Edge) :
    wordCoefficient e (P.orientedBoundary f)=paritySign f.orientation*wordCoefficient e (P.boundary f.face):=by
  cases f with
  | mk f b=>cases b <;> simp [orientedBoundary,paritySign,wordCoefficient_inverse]

/-- A coherent choice of actual face traversals balances every oriented edge incidence. -/
def CoherentSigns (P:FiniteCyclicPresentation) (ε:P.Face→ℤ) :Prop:=
  (∀f,ε f=1 ∨ ε f= -1) ∧
    ∀e:P.Edge,∑f:P.Face,ε f*wordCoefficient e (P.boundary f)=0

/-- Closed coherent orientability is an existential choice of genuine face signs. -/
def IsCoherentlyOrientable (P:FiniteCyclicPresentation) :Prop:=∃ε,CoherentSigns P ε

theorem dartCoefficient_relabel {E F:Type} [DecidableEq E] [DecidableEq F]
    (r:EdgeRelabeling E F) (a:E) (d:SignedDart E) :
    dartCoefficient (r.edgeEquiv a) (r.mapDart d)=paritySign (r.reverse a)*dartCoefficient a d:=by
  cases d with
  | pos b=>
    by_cases h:b=a
    · subst b;cases hb:r.reverse a <;> simp [EdgeRelabeling.mapDart,dartCoefficient,paritySign,hb]
    · have he:r.edgeEquiv b≠r.edgeEquiv a:=r.edgeEquiv.injective.ne h
      cases hb:r.reverse b <;> simp [EdgeRelabeling.mapDart,dartCoefficient,he,h,paritySign,hb]
  | neg b=>
    by_cases h:b=a
    · subst b;cases hb:r.reverse a <;> simp [EdgeRelabeling.mapDart,dartCoefficient,paritySign,hb]
    · have he:r.edgeEquiv b≠r.edgeEquiv a:=r.edgeEquiv.injective.ne h
      cases hb:r.reverse b <;> simp [EdgeRelabeling.mapDart,dartCoefficient,he,h,paritySign,hb]

theorem wordCoefficient_relabel {E F:Type} [DecidableEq E] [DecidableEq F]
    (r:EdgeRelabeling E F) (a:E) (w:List (SignedDart E)) :
    wordCoefficient (r.edgeEquiv a) (w.map r.mapDart)=paritySign (r.reverse a)*wordCoefficient a w:=by
  induction w with
  | nil=>simp only [List.map_nil,wordCoefficient_nil,mul_zero]
  | cons d w ih=>
    rw [List.map_cons,wordCoefficient_cons,dartCoefficient_relabel,ih,wordCoefficient_cons,mul_add]

theorem unit_mul_parity (x:ℤ) (hx:x=1 ∨ x= -1) (b:Bool) :
    x*paritySign b=1 ∨ x*paritySign b= -1 :=by
  rcases hx with rfl|rfl <;> cases b <;> decide

/-- Independent reversals of genuine face and edge orientations preserve the
existence of a coherent face orientation. The signed incidence matrix is reindexed exactly. -/
theorem coherent_reindex_iff {P Q:FiniteCyclicPresentation}
    (fe:P.Face≃Q.Face) (ee:P.Edge≃Q.Edge) (fr:P.Face→Bool) (er:P.Edge→Bool)
    (hm:∀f a,paritySign (er a)*wordCoefficient a (P.boundary f)=
      paritySign (fr f)*wordCoefficient (ee a) (Q.boundary (fe f))) :
    IsCoherentlyOrientable P↔IsCoherentlyOrientable Q :=by
  constructor
  · rintro ⟨ε,hε⟩
    let η:Q.Face→ℤ:=fun q=>ε (fe.symm q)*paritySign (fr (fe.symm q))
    refine ⟨η,fun q=>unit_mul_parity _ (hε.1 _) _,?_⟩
    intro b
    obtain ⟨a,rfl⟩:=ee.surjective b
    calc
      ∑q:Q.Face,η q*wordCoefficient (ee a) (Q.boundary q)=
          ∑f:P.Face,η (fe f)*wordCoefficient (ee a) (Q.boundary (fe f)):=
        (Fintype.sum_equiv fe _ _ (fun _=>rfl)).symm
      _=∑f:P.Face,paritySign (er a)*(ε f*wordCoefficient a (P.boundary f)):=by
        apply Finset.sum_congr rfl
        intro f _
        dsimp only [η]
        rw [fe.symm_apply_apply,mul_assoc,←hm]
        ring
      _=paritySign (er a)*(∑f:P.Face,ε f*wordCoefficient a (P.boundary f)):=by rw [Finset.mul_sum]
      _=0:=by rw [hε.2 a,mul_zero]
  · rintro ⟨η,hη⟩
    let ε:P.Face→ℤ:=fun f=>η (fe f)*paritySign (fr f)
    refine ⟨ε,fun f=>unit_mul_parity _ (hη.1 _) _,?_⟩
    intro a
    have he:paritySign (er a)*(∑f:P.Face,ε f*wordCoefficient a (P.boundary f))=0:=by
      calc
        paritySign (er a)*(∑f:P.Face,ε f*wordCoefficient a (P.boundary f))=
            ∑f:P.Face,paritySign (er a)*(ε f*wordCoefficient a (P.boundary f)):=by rw [Finset.mul_sum]
        _=∑f:P.Face,η (fe f)*wordCoefficient (ee a) (Q.boundary (fe f)):=by
          apply Finset.sum_congr rfl
          intro f _
          dsimp only [ε]
          calc
            paritySign (er a)*((η (fe f)*paritySign (fr f))*wordCoefficient a (P.boundary f))=
                η (fe f)*paritySign (fr f)*(paritySign (er a)*wordCoefficient a (P.boundary f)):=by ring
            _=η (fe f)*paritySign (fr f)*(paritySign (fr f)*wordCoefficient (ee a) (Q.boundary (fe f))):=by rw [hm]
            _=η (fe f)*(paritySign (fr f)*paritySign (fr f))*wordCoefficient (ee a) (Q.boundary (fe f)):=by ring
            _=η (fe f)*wordCoefficient (ee a) (Q.boundary (fe f)):=by rw [paritySign_sq,mul_one]
        _=∑q:Q.Face,η q*wordCoefficient (ee a) (Q.boundary q):=
          Fintype.sum_equiv fe _ _ (fun _=>rfl)
        _=0:=hη.2 (ee a)
    exact (mul_eq_zero.mp he).resolve_left (paritySign_ne_zero _)

theorem unorientedIso_coherent_iff {P Q:FiniteCyclicPresentation} (e:UnorientedPresentationIso P Q) :
    IsCoherentlyOrientable P↔IsCoherentlyOrientable Q :=by
  apply coherent_reindex_iff e.faceEquiv e.edgeEquiv e.reverseFace e.edgeRelabeling.reverse
  intro f a
  have hh:=wordCoefficient_rotated (e.edgeEquiv a) (e.boundary_rotated f)
  rw [wordCoefficient_relabel,orientedBoundary_coefficient] at hh
  exact hh

theorem signedIso_coherent_iff {P Q:FiniteCyclicPresentation} (e:SignedPresentationIso P Q) :
    IsCoherentlyOrientable P↔IsCoherentlyOrientable Q :=
  unorientedIso_coherent_iff (UnorientedPresentationIso.ofSignedPresentationIso e)

theorem p1_dart_coefficient_old {n:ℕ} (a e:Fin n) (d:SignedDart (Fin n)) :
    wordCoefficient e.castSucc (P1.expandDart a d)=dartCoefficient e d :=by
  cases d with
  | pos b=>
    by_cases hb:b=a
    · subst b
      simp [P1.expandDart,P1.firstSubedge,P1.freshEdge,wordCoefficient,dartCoefficient,
        (Fin.castSucc_ne_last e).symm]
    · simp [P1.expandDart,wordCoefficient,dartCoefficient,hb]
  | neg b=>
    by_cases hb:b=a
    · subst b
      simp [P1.expandDart,P1.firstSubedge,P1.freshEdge,wordCoefficient,dartCoefficient,
        (Fin.castSucc_ne_last e).symm]
    · simp [P1.expandDart,wordCoefficient,dartCoefficient,hb]

theorem p1_dart_coefficient_fresh {n:ℕ} (a:Fin n) (d:SignedDart (Fin n)) :
    wordCoefficient (P1.freshEdge n) (P1.expandDart a d)=dartCoefficient a d :=by
  cases d with
  | pos b=>
    by_cases hb:b=a
    · subst b
      simp [P1.expandDart,P1.firstSubedge,P1.freshEdge,wordCoefficient,dartCoefficient]
    · simp [P1.expandDart,P1.freshEdge,wordCoefficient,dartCoefficient,hb]
  | neg b=>
    by_cases hb:b=a
    · subst b
      simp [P1.expandDart,P1.firstSubedge,P1.freshEdge,wordCoefficient,dartCoefficient]
    · simp [P1.expandDart,P1.freshEdge,wordCoefficient,dartCoefficient,hb]

theorem p1_word_coefficient_old {n:ℕ} (a e:Fin n) (w:List (SignedDart (Fin n))) :
    wordCoefficient e.castSucc (P1.expandWord a w)=wordCoefficient e w :=by
  induction w with
  | nil=>rfl
  | cons d w ih=>
    rw [show P1.expandWord a (d::w)=P1.expandDart a d++P1.expandWord a w by rfl,
      wordCoefficient_append,p1_dart_coefficient_old,ih,wordCoefficient_cons]

theorem p1_word_coefficient_fresh {n:ℕ} (a:Fin n) (w:List (SignedDart (Fin n))) :
    wordCoefficient (P1.freshEdge n) (P1.expandWord a w)=wordCoefficient a w :=by
  induction w with
  | nil=>rfl
  | cons d w ih=>
    rw [show P1.expandWord a (d::w)=P1.expandDart a d++P1.expandWord a w by rfl,
      wordCoefficient_append,p1_dart_coefficient_fresh,ih,wordCoefficient_cons]

theorem p1_coherent_iff (P:FiniteCyclicPresentation) (a:P.Edge) :
    IsCoherentlyOrientable P↔IsCoherentlyOrientable (P1.expand P a) :=by
  let fe:=P1.faceEquiv P a
  constructor
  · rintro ⟨ε,hε⟩
    let η:(P1.expand P a).Face→ℤ:=fun f=>ε (fe.symm f)
    refine ⟨η,fun f=>hε.1 _,?_⟩
    intro b
    have he:(∑q:(P1.expand P a).Face,η q*wordCoefficient b ((P1.expand P a).boundary q))=
        ∑f:P.Face,ε f*wordCoefficient b (P1.expandWord a (P.boundary f)):=by
      rw [←Fintype.sum_equiv fe _ _ (fun _=>rfl)]
      apply Finset.sum_congr rfl
      intro f _
      simp only [η,fe,Equiv.symm_apply_apply,P1.expand_boundary]
    rw [he]
    refine Fin.lastCases ?_ (fun e=>?_) b
    · change ∑f:P.Face,ε f*wordCoefficient (P1.freshEdge P.edgeCount) (P1.expandWord a (P.boundary f))=0
      simp only [p1_word_coefficient_fresh]
      exact hε.2 a
    · simp only [p1_word_coefficient_old]
      exact hε.2 e
  · rintro ⟨η,hη⟩
    let ε:P.Face→ℤ:=fun f=>η (fe f)
    refine ⟨ε,fun f=>hη.1 _,?_⟩
    intro e
    calc
      ∑f:P.Face,ε f*wordCoefficient e (P.boundary f)=
          ∑f:P.Face,η (fe f)*wordCoefficient e.castSucc ((P1.expand P a).boundary (fe f)):=by
        apply Finset.sum_congr rfl
        intro f _
        simp only [ε,fe,P1.expand_boundary,p1_word_coefficient_old]
      _=∑q:(P1.expand P a).Face,η q*wordCoefficient e.castSucc ((P1.expand P a).boundary q):=
        Fintype.sum_equiv fe _ _ (fun _=>rfl)
      _=0:=hη.2 e.castSucc

theorem p2_retain_coefficient_old {n:ℕ} (e:Fin n) (w:List (SignedDart (Fin n))) :
    wordCoefficient e.castSucc (P2.retainWord w)=wordCoefficient e w :=by
  induction w with
  | nil=>rfl
  | cons d w ih=>
    change dartCoefficient e.castSucc (P1.castSuccDart d)+wordCoefficient e.castSucc (P2.retainWord w)=_
    rw [ih,wordCoefficient_cons]
    congr 1
    cases d <;> simp [P1.castSuccDart,dartCoefficient]

theorem p2_retain_coefficient_fresh {n:ℕ} (w:List (SignedDart (Fin n))) :
    wordCoefficient (P1.freshEdge n) (P2.retainWord w)=0 :=by
  induction w with
  | nil=>rfl
  | cons d w ih=>
    change dartCoefficient (P1.freshEdge n) (P1.castSuccDart d)+wordCoefficient (P1.freshEdge n) (P2.retainWord w)=_
    rw [ih,add_zero]
    cases d <;> simp [P1.castSuccDart,P1.freshEdge,dartCoefficient]

theorem p2_stored_coefficient {E:Type} [DecidableEq E] (b:Bool) (e:E) (w:List (SignedDart E)) :
    wordCoefficient e (P2.storedWord b w)=paritySign b*wordCoefficient e w:=by
  cases b <;> simp [P2.storedWord,paritySign,wordCoefficient_inverse]

theorem p2_selected_coefficient_old (P:FiniteCyclicPresentation) (cut:P2Cut P) (e:P.Edge) :
    wordCoefficient e.castSucc ((P2.split P cut).boundary (P2.oldFace P cut cut.face.face))=
      paritySign cut.face.orientation*wordCoefficient e cut.left :=by
  rw [P2.split_boundary_selected,P2.selectedBoundary,p2_stored_coefficient,
    P2.selectedOrientedBoundary,wordCoefficient_append,p2_retain_coefficient_old,
    wordCoefficient_cons,wordCoefficient_nil]
  simp [dartCoefficient,P2.freshEdge,P1.freshEdge,(Fin.castSucc_ne_last e).symm]

theorem p2_right_coefficient_old (P:FiniteCyclicPresentation) (cut:P2Cut P) (e:P.Edge) :
    wordCoefficient e.castSucc ((P2.split P cut).boundary (P2.rightFace P cut))=
      paritySign cut.face.orientation*wordCoefficient e cut.right :=by
  rw [P2.split_boundary_right,P2.rightBoundary,p2_stored_coefficient,
    P2.rightOrientedBoundary,wordCoefficient_cons,p2_retain_coefficient_old]
  simp [dartCoefficient,P2.freshEdge,P1.freshEdge,(Fin.castSucc_ne_last e).symm]

theorem p2_other_coefficient_old (P:FiniteCyclicPresentation) (cut:P2Cut P) (f:P.Face)
    (hf:f≠cut.face.face) (e:P.Edge) :
    wordCoefficient e.castSucc ((P2.split P cut).boundary (P2.oldFace P cut f))=
      wordCoefficient e (P.boundary f) :=by
  rw [P2.split_boundary_old_of_ne P cut hf,p2_retain_coefficient_old]

theorem p2_selected_coefficient_fresh (P:FiniteCyclicPresentation) (cut:P2Cut P) :
    wordCoefficient (P2.freshEdge P) ((P2.split P cut).boundary (P2.oldFace P cut cut.face.face))=
      paritySign cut.face.orientation :=by
  rw [P2.split_boundary_selected,P2.selectedBoundary,p2_stored_coefficient,
    P2.selectedOrientedBoundary,wordCoefficient_append]
  change paritySign cut.face.orientation*(wordCoefficient (P1.freshEdge P.edgeCount) (P2.retainWord cut.left)+
    wordCoefficient (P2.freshEdge P) [.pos (P2.freshEdge P)])=_
  rw [p2_retain_coefficient_fresh]
  simp [wordCoefficient,dartCoefficient]

theorem p2_right_coefficient_fresh (P:FiniteCyclicPresentation) (cut:P2Cut P) :
    wordCoefficient (P2.freshEdge P) ((P2.split P cut).boundary (P2.rightFace P cut))=
      -paritySign cut.face.orientation :=by
  rw [P2.split_boundary_right,P2.rightBoundary,p2_stored_coefficient,
    P2.rightOrientedBoundary,wordCoefficient_cons]
  change paritySign cut.face.orientation*(dartCoefficient (P2.freshEdge P) (.neg (P2.freshEdge P))+
    wordCoefficient (P1.freshEdge P.edgeCount) (P2.retainWord cut.right))=_
  rw [p2_retain_coefficient_fresh]
  simp [dartCoefficient]

theorem p2_other_coefficient_fresh (P:FiniteCyclicPresentation) (cut:P2Cut P) (f:P.Face)
    (hf:f≠cut.face.face) :
    wordCoefficient (P2.freshEdge P) ((P2.split P cut).boundary (P2.oldFace P cut f))=0 :=by
  rw [P2.split_boundary_old_of_ne P cut hf]
  exact p2_retain_coefficient_fresh _

theorem p2_cut_coefficient (P:FiniteCyclicPresentation) (cut:P2Cut P) (e:P.Edge) :
    paritySign cut.face.orientation*wordCoefficient e (P.boundary cut.face.face)=
      wordCoefficient e cut.left+wordCoefficient e cut.right :=by
  have hh:=wordCoefficient_rotated e cut.boundary_rotated
  rw [orientedBoundary_coefficient,wordCoefficient_append] at hh
  exact hh

theorem p2_sum_faces (P:FiniteCyclicPresentation) (cut:P2Cut P) (F:(P2.split P cut).Face→ℤ) :
    (∑q:(P2.split P cut).Face,F q)=(∑f:P.Face,F (P2.oldFace P cut f))+F (P2.rightFace P cut) :=by
  rw [←Fintype.sum_equiv (P2.faceEquiv P cut) _ _ (fun _=>rfl),Fin.sum_univ_castSucc]
  rfl

def p2FaceSigns (P:FiniteCyclicPresentation) (cut:P2Cut P) (ε:P.Face→ℤ) :
    (P2.split P cut).Face→ℤ:=
  fun q=>Fin.lastCases (ε cut.face.face) ε ((P2.faceEquiv P cut).symm q)

theorem p2FaceSigns_old (P:FiniteCyclicPresentation) (cut:P2Cut P) (ε:P.Face→ℤ) (f:P.Face) :
    p2FaceSigns P cut ε (P2.oldFace P cut f)=ε f:=by
  simp [p2FaceSigns,P2.oldFace]

theorem p2FaceSigns_right (P:FiniteCyclicPresentation) (cut:P2Cut P) (ε:P.Face→ℤ) :
    p2FaceSigns P cut ε (P2.rightFace P cut)=ε cut.face.face:=by
  simp [p2FaceSigns,P2.rightFace]

theorem sum_replace_add {A:Type} [Fintype A] [DecidableEq A] (f:A→ℤ) (a:A) (x y:ℤ)
    (h:x+y=f a) : (∑b:A,if b=a then x else f b)+y=∑b:A,f b:=by
  have hy:(∑b:A,if b=a then y else 0)=y:=by simp
  calc
    (∑b:A,if b=a then x else f b)+y=
        (∑b:A,if b=a then x else f b)+(∑b:A,if b=a then y else 0):=by rw [hy]
    _=∑b:A,((if b=a then x else f b)+(if b=a then y else 0)):=by rw [Finset.sum_add_distrib]
    _=∑b:A,f b:=by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb:b=a
      · subst b;simpa using h
      · simp only [ite_eq_right hb,add_zero]

theorem p2_signed_incidence_old (P:FiniteCyclicPresentation) (cut:P2Cut P) (ε:P.Face→ℤ) (e:P.Edge) :
    (∑q:(P2.split P cut).Face,p2FaceSigns P cut ε q*wordCoefficient e.castSucc ((P2.split P cut).boundary q))=
      ∑f:P.Face,ε f*wordCoefficient e (P.boundary f) :=by
  rw [p2_sum_faces,p2FaceSigns_right,p2_right_coefficient_old]
  have hold:(∑f:P.Face,p2FaceSigns P cut ε (P2.oldFace P cut f)*
      wordCoefficient e.castSucc ((P2.split P cut).boundary (P2.oldFace P cut f)))=
      ∑f:P.Face,if f=cut.face.face then
        ε cut.face.face*(paritySign cut.face.orientation*wordCoefficient e cut.left)
      else ε f*wordCoefficient e (P.boundary f):=by
    apply Finset.sum_congr rfl
    intro f _
    rw [p2FaceSigns_old]
    by_cases hf:f=cut.face.face
    · subst f;rw [ite_eq_left rfl,p2_selected_coefficient_old]
    · rw [ite_eq_right hf,p2_other_coefficient_old P cut f hf]
  rw [hold]
  apply sum_replace_add
  have hc:=p2_cut_coefficient P cut e
  have he:paritySign cut.face.orientation*(wordCoefficient e cut.left+wordCoefficient e cut.right)=
      wordCoefficient e (P.boundary cut.face.face):=by
    rw [←hc,←mul_assoc,paritySign_sq,one_mul]
  rw [←he]
  ring

theorem p2_signed_incidence_fresh (P:FiniteCyclicPresentation) (cut:P2Cut P)
    (η:(P2.split P cut).Face→ℤ) :
    (∑q:(P2.split P cut).Face,η q*wordCoefficient (P2.freshEdge P) ((P2.split P cut).boundary q))=
      (η (P2.oldFace P cut cut.face.face)-η (P2.rightFace P cut))*paritySign cut.face.orientation :=by
  rw [p2_sum_faces,p2_right_coefficient_fresh]
  have hold:(∑f:P.Face,η (P2.oldFace P cut f)*
      wordCoefficient (P2.freshEdge P) ((P2.split P cut).boundary (P2.oldFace P cut f)))=
      η (P2.oldFace P cut cut.face.face)*paritySign cut.face.orientation:=by
    calc
      _=∑f:P.Face,if f=cut.face.face then
          η (P2.oldFace P cut cut.face.face)*paritySign cut.face.orientation else 0:=by
        apply Finset.sum_congr rfl
        intro f _
        by_cases hf:f=cut.face.face
        · subst f;rw [ite_eq_left rfl,p2_selected_coefficient_fresh]
        · rw [ite_eq_right hf,p2_other_coefficient_fresh P cut f hf,mul_zero]
      _= _:=by simp
  rw [hold]
  ring

theorem p2_coherent_iff (P:FiniteCyclicPresentation) (cut:P2Cut P) :
    IsCoherentlyOrientable P↔IsCoherentlyOrientable (P2.split P cut) :=by
  constructor
  · rintro ⟨ε,hε⟩
    refine ⟨p2FaceSigns P cut ε,?_,?_⟩
    · intro q
      rcases P2.face_cases P cut q with ⟨f,rfl⟩|rfl
      · rw [p2FaceSigns_old];exact hε.1 f
      · rw [p2FaceSigns_right];exact hε.1 _
    · intro e
      refine Fin.lastCases ?_ (fun a=>?_) e
      · change ∑q:(P2.split P cut).Face,p2FaceSigns P cut ε q*
          wordCoefficient (P2.freshEdge P) ((P2.split P cut).boundary q)=0
        rw [p2_signed_incidence_fresh,p2FaceSigns_old,p2FaceSigns_right,sub_self,zero_mul]
      · rw [p2_signed_incidence_old]
        exact hε.2 a
  · rintro ⟨η,hη⟩
    let ε:P.Face→ℤ:=fun f=>η (P2.oldFace P cut f)
    have hchildren:η (P2.oldFace P cut cut.face.face)=η (P2.rightFace P cut):=by
      have hh:=hη.2 (P2.freshEdge P)
      rw [p2_signed_incidence_fresh] at hh
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (paritySign_ne_zero _))
    have he:p2FaceSigns P cut ε=η:=by
      funext q
      rcases P2.face_cases P cut q with ⟨f,rfl⟩|rfl
      · exact p2FaceSigns_old P cut ε f
      · rw [p2FaceSigns_right]
        exact hchildren
    refine ⟨ε,fun f=>hη.1 _,?_⟩
    intro e
    rw [←p2_signed_incidence_old P cut ε e,he]
    exact hη.2 e.castSucc

theorem subdivisionStep_coherent_iff {P Q:FiniteCyclicPresentation} (h:SubdivisionStep P Q) :
    IsCoherentlyOrientable P↔IsCoherentlyOrientable Q :=by
  rcases h with hi|h|h
  · obtain ⟨e⟩:=hi
    exact signedIso_coherent_iff e
  · obtain ⟨a,⟨e⟩⟩:=h
    exact (p1_coherent_iff P a).trans (signedIso_coherent_iff e)
  · obtain ⟨cut,_,⟨e⟩⟩:=h
    exact (p2_coherent_iff P cut).trans (signedIso_coherent_iff e)

theorem subdivides_coherent_iff {P Q:FiniteCyclicPresentation} (h:Subdivides P Q) :
    IsCoherentlyOrientable P↔IsCoherentlyOrientable Q :=by
  induction h with
  | refl=>exact Iff.rfl
  | tail _ hs ih=>exact ih.trans (subdivisionStep_coherent_iff hs)

theorem commonSubdivision_coherent_iff {P Q:FiniteCyclicPresentation} (h:HasCommonSubdivision P Q) :
    IsCoherentlyOrientable P↔IsCoherentlyOrientable Q :=by
  obtain ⟨R,hPR,hQR⟩:=h
  exact (subdivides_coherent_iff hPR).trans (subdivides_coherent_iff hQR).symm

theorem normalizationStep_coherent_iff {P Q:ValidPresentation} (h:NormalizationStep P Q) :
    IsCoherentlyOrientable P.presentation↔IsCoherentlyOrientable Q.presentation :=by
  cases h with
  | commonSubdivision h=>exact commonSubdivision_coherent_iff h
  | unoriented h=>
    rcases h with hf|hb
    · obtain ⟨e⟩:=hf
      exact unorientedIso_coherent_iff e
    · obtain ⟨e⟩:=hb
      exact (unorientedIso_coherent_iff e).symm
  | oneSidedP2 cut _=>exact p2_coherent_iff _ cut

theorem normalizationEquivalent_coherent_iff {P Q:ValidPresentation} (h:NormalizationEquivalent P Q) :
    IsCoherentlyOrientable P.presentation↔IsCoherentlyOrientable Q.presentation :=by
  induction h with
  | rel _ _ h=>exact normalizationStep_coherent_iff h
  | refl=>exact Iff.rfl
  | symm _ _ _ ih=>exact ih.symm
  | trans _ _ _ _ _ ih ij=>exact ih.trans ij

theorem normalizationResult_coherent_iff {P:ValidPresentation} (r:NormalizationResult P) :
    IsCoherentlyOrientable P.presentation↔IsCoherentlyOrientable r.normalForm.canonicalPresentation:=
  normalizationEquivalent_coherent_iff r.equivalent

theorem oneFace_boundary_coefficient {E:Type} [Fintype E] [DecidableEq E]
    (w:List (SignedDart E)) (a:E) (f:(ofOneFaceWord w).Face) :
    wordCoefficient (ofOneFaceWordEdgeEquiv w a) ((ofOneFaceWord w).boundary f)=wordCoefficient a w:=by
  rw [ofOneFaceWord_boundary]
  have hh:=wordCoefficient_relabel (EdgeRelabeling.ofEquiv (Fintype.equivFin E)) a w
  rw [EdgeRelabeling.map_mapDart_ofEquiv] at hh
  simpa [EdgeRelabeling.ofEquiv,ofOneFaceWordEdgeEquiv,paritySign] using hh

theorem oneFace_coherent_iff {E:Type} [Fintype E] [DecidableEq E]
    (w:List (SignedDart E)) :IsCoherentlyOrientable (ofOneFaceWord w)↔∀a:E,wordCoefficient a w=0:=by
  constructor
  · rintro ⟨ε,hε⟩ a
    have hh:=hε.2 (ofOneFaceWordEdgeEquiv w a)
    change (∑f:Fin 1,ε f*wordCoefficient (ofOneFaceWordEdgeEquiv w a) ((ofOneFaceWord w).boundary f))=0 at hh
    rw [Fin.sum_univ_one,oneFace_boundary_coefficient] at hh
    have hunit:ε 0≠0:=by rcases hε.1 0 with h|h <;> rw [h] <;> norm_num
    exact (mul_eq_zero.mp hh).resolve_left hunit
  · intro h
    refine ⟨fun _=>1,fun _=>Or.inl rfl,?_⟩
    intro e
    obtain ⟨a,rfl⟩:=(ofOneFaceWordEdgeEquiv w).surjective e
    simp only [oneFace_boundary_coefficient,h a,mul_zero,Finset.sum_const_zero]

theorem nonorientable_crosscap_coefficient (p b:ℕ) (i:Fin p) :
    wordCoefficient (NormalForm.NonOrientableEdge.a i) (NormalForm.nonOrientableBoundaryWord p b)=2:=by
  simp [NormalForm.nonOrientableBoundaryWord,NormalForm.nonOrientableCrosscapBlock,
    NormalForm.nonOrientableBoundaryBlock,wordCoefficient,dartCoefficient,List.map_flatten,
    List.sum_flatten,List.sum_ofFn,Finset.sum_add_distrib]

theorem nonorientableCanonical_not_coherent (p b:ℕ) (hp:0<p) :
    ¬IsCoherentlyOrientable (NormalForm.nonOrientable p b).canonicalPresentation:=by
  rw [NormalForm.canonicalPresentation_nonOrientable,oneFace_coherent_iff]
  intro h
  have hh:=h (NormalForm.NonOrientableEdge.a ⟨0,hp⟩)
  rw [nonorientable_crosscap_coefficient] at hh
  norm_num at hh

/-- Closed coherent input normalizes only to the sphere or a closed orientable canonical
surface. Crosscap endpoints are excluded by their actual signed edge incidence. -/
theorem closed_coherent_normalizationResult {P:ValidPresentation} (r:NormalizationResult P)
    (hc:IsClosed P.presentation) (ho:IsCoherentlyOrientable P.presentation) :
    r.normalForm=.sphere ∨∃g,r.normalForm=.orientable g 0 :=by
  have hON:IsCoherentlyOrientable r.normalForm.canonicalPresentation:=(normalizationResult_coherent_iff r).mp ho
  rcases closed_normalizationResult_boundary_zero r hc with hs|hg|hn
  · exact Or.inl hs
  · exact Or.inr hg
  · obtain ⟨g,hg⟩:=hn
    have had:1≤g:=by simpa only [hg,NormalForm.IsEvalAdmissible] using r.admissible
    exact False.elim (nonorientableCanonical_not_coherent g 0 (by omega) (hg ▸ hON))

end LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
