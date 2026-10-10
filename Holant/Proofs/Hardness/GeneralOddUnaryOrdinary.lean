import Holant.Proofs.Hardness.GeneralOddUnaryEscape
import Holant.Holographic
import Holant.Tractable.Downward

/-! The unary-escape producer returned to the actual ordinary family.
K coordinates are analytical only.  The output has the original vertex
signatures, original port order, and ordinary Eq edges, with no new scalar
normalization.  An isotropic unary plus actual both-sign support produces
an independent unary.  Independence is not asserted to imply hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnaryOrdinary
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
namespace Open
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [CommSemiring K] {n : ℕ}

def assignments (s : NetworkShape n) :
    ((Fin n → Bool) × ((Fin s.edges × Bool) → Bool)) ≃
      ((v : Fin s.vertices) → Fin (s.arity v) → Bool) :=
  (Equiv.sumArrowEquivProdArrow (Fin n) (Fin s.edges × Bool) Bool).symm.trans
    ((Equiv.arrowCongr s.ports.symm (Equiv.refl Bool)).trans
      (Equiv.piCurry fun (v : Fin s.vertices) (_ : Fin (s.arity v)) => Bool))

theorem prod_ports (s : NetworkShape n) (f : Fin n ⊕ (Fin s.edges × Bool) → K) :
    (∏ v, ∏ i, f (s.ports ⟨v,i⟩)) =
      (∏ i : Fin n, f (.inl i)) * ∏ q : Fin s.edges × Bool, f (.inr q) := by
  rw [←Fintype.prod_sigma (fun p => f (s.ports p)),s.ports.prod_comp,
    Fintype.prod_sum_type]

theorem prod_vertex_action (s : NetworkShape n)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) (A : Kernel K)
    (x : Fin n → Bool) (z : (Fin s.edges × Bool) → Bool) :
    (∏ v, Signature.coordinateAction (fun _ => A) (f v) (s.assignment x z v)) =
      ∑ y : Fin n → Bool, ∑ w : (Fin s.edges × Bool) → Bool,
        (∏ i, A (x i) (y i)) * (∏ q, A (z q) (w q)) *
          ∏ v, f v (s.assignment y w v) := by
  classical
  simp only [Signature.coordinateAction]
  rw [Fintype.prod_sum,←(assignments s).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.prod_mul_distrib]
  have hp := prod_ports s (fun p => A (Sum.elim x z p) (Sum.elim y w p))
  change (∏ v, ∏ i, A (Sum.elim x z (s.ports ⟨v,i⟩))
    (Sum.elim y w (s.ports ⟨v,i⟩))) *
      (∏ v, f v (s.assignment y w v)) = _
  rw [hp]
  rfl

def transform (N : Network K n) (M A : Kernel K) : Network K n where
  shape := N.shape
  vertex v := Signature.coordinateAction (fun _ => A) (N.vertex v)
  edge e := Kernel.pullback (N.edge e) M

theorem transform_denote (N : Network K n) (M A : Kernel K)
    (hMA : Kernel.mul M A = Signature.equality) :
    (transform N M A).denote = Signature.coordinateAction (fun _ => A) N.denote := by
  classical
  funext x
  change (∑ z, (∏ v, Signature.coordinateAction (fun _ => A) (N.vertex v)
    (N.shape.assignment x z v)) * ∏ e,
    Kernel.pullback (N.edge e) M (z (e,false)) (z (e,true))) =
    ∑ y, (∏ i, A (x i) (y i)) * N.denote y
  simp_rw [prod_vertex_action]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Network.denote,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  calc
    _ = ((∏ i, A (x i) (y i)) * ∏ v, N.vertex v (N.shape.assignment y w v)) *
        ∑ z : (Fin N.shape.edges × Bool) → Bool,
          (∏ q, A (z q) (w q)) * ∏ e,
            Kernel.pullback (N.edge e) M (z (e,false)) (z (e,true)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ac_rfl
    _ = _ := by rw [Network.sum_edge_action _ _ M A hMA]; ac_rfl
end Open
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def Ordinary (N : Network AlgebraicComplex n) : Prop :=
  ∀ e,N.edge e=Signature.equality

def toNative (N : Network AlgebraicComplex n) : Network AlgebraicComplex n :=
  Open.transform N sourceKBasis.matrix sourceKBasis.inverse

def toOrdinary (N : Network AlgebraicComplex n) : Network AlgebraicComplex n :=
  Open.transform N sourceKBasis.inverse sourceKBasis.matrix

theorem toNative_denote (N : Network AlgebraicComplex n) :
    (toNative N).denote=sourceKBasis.symm.action N.denote :=
  Open.transform_denote N _ _ sourceKBasis.matrix_inverse

theorem toOrdinary_denote (N : Network AlgebraicComplex n) :
    (toOrdinary N).denote=sourceKBasis.action N.denote :=
  Open.transform_denote N _ _ sourceKBasis.inverse_matrix

theorem toNative_native (N : Network AlgebraicComplex n) (hN : Ordinary N) :
    Native (toNative N) := by
  intro e
  change Kernel.pullback (N.edge e) sourceKBasis.matrix=Signature.disequality
  rw [hN e,sourceKBasis_pullback]

theorem toOrdinary_ordinary (N : Network AlgebraicComplex n) (hN : Native N) :
    Ordinary (toOrdinary N) := by
  intro e
  change Kernel.pullback (N.edge e) sourceKBasis.inverse=Signature.equality
  rw [hN e,←sourceKBasis_pullback,←pullback_mul,sourceKBasis.matrix_inverse]
  simp [Kernel.pullback]

theorem toNative_uses (F : SignatureFamily AlgebraicComplex)
    (N : Network AlgebraicComplex n) (hN : Uses N F) :
    Uses (toNative N) (kCoordinates F) := by
  intro v
  exact ⟨⟨N.shape.arity v,N.vertex v⟩,hN v,rfl⟩

theorem toOrdinary_uses (F : SignatureFamily AlgebraicComplex)
    (N : Network AlgebraicComplex n) (hN : Uses N (kCoordinates F)) :
    Uses (toOrdinary N) F := by
  intro v
  obtain ⟨⟨m,f⟩,hf,he⟩ := hN v
  have hn : m=N.shape.arity v := congrArg Sigma.fst he
  subst m
  have hv : sourceKBasis.symm.action f=N.vertex v := by
    exact eq_of_heq (Sigma.mk.inj he).2
  change (⟨N.shape.arity v,sourceKBasis.action (N.vertex v)⟩ : AnySignature AlgebraicComplex)∈F
  rw [←hv,InvertibleKernel.action_symm_action]
  exact hf

def pairing (f g : Signature AlgebraicComplex 1) : AlgebraicComplex :=
  Signature.connect Signature.equality (fun b => f (fun _ => b)) (fun b => g (fun _ => b))

def determinant (f g : Signature AlgebraicComplex 1) : AlgebraicComplex :=
  f (fun _ => false)*g (fun _ => true)-f (fun _ => true)*g (fun _ => false)

theorem gram_identity (f g : Signature AlgebraicComplex 1) :
    determinant f g^2=pairing f f*pairing g g-pairing f g^2 := by
  simp only [determinant,pairing,Signature.connect_equality]
  ring

/-- Nonzero cross pairing with an isotropic first row gives a genuine basis
of the two-dimensional unary space. This is not a hardness assertion. -/
theorem independent_of_isotropic (f g : Signature AlgebraicComplex 1)
    (hf : pairing f f=0) (hfg : pairing f g≠0) : determinant f g≠0 := by
  intro hd
  have h := gram_identity f g
  have hs : -(pairing f g^2)=0 := by simpa [hd,hf] using h.symm
  exact pow_ne_zero 2 hfg (neg_eq_zero.mp hs)

private theorem unary_vector (f : Signature AlgebraicComplex 1) (b : Bool) :
    sourceKBasis.action f (fun _ => b)=
      Kernel.act sourceKBasis.matrix (fun a => f (fun _ => a)) b := by
  change (∑y : Fin 1 → Bool,(∏i : Fin 1,sourceKBasis.matrix b (y i))*f y)=_
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp only [Fin.prod_univ_one]
  rfl

theorem pairing_action (f g : Signature AlgebraicComplex 1) :
    pairing (sourceKBasis.action f) (sourceKBasis.action g)=
      f (fun _ => false)*g (fun _ => true)+f (fun _ => true)*g (fun _ => false) := by
  unfold pairing
  simp_rw [unary_vector]
  rw [Kernel.connect_act_same,sourceKBasis_pullback,Signature.connect_disequality]

theorem pairing_diagnostic (f g : Signature AlgebraicComplex 1) :
    pairing f g=
      sourceKBasis.symm.action f (fun _ => false)*sourceKBasis.symm.action g (fun _ => true)+
      sourceKBasis.symm.action f (fun _ => true)*sourceKBasis.symm.action g (fun _ => false) := by
  simpa only [InvertibleKernel.action_symm_action] using
    pairing_action (sourceKBasis.symm.action f) (sourceKBasis.symm.action g)

theorem unary_word (x : Fin 1 → Bool) : x=(fun _ => x 0) := by
  funext i
  exact congrArg x (Subsingleton.elim _ _)

/-- Isotropy is classified from the actual two entries.  The coefficient is
retained; in particular the graph is never divided by it. -/
theorem isotropic_diagnostic (f : Signature AlgebraicComplex 1)
    (hf : f≠0) (hiso : pairing f f=0) :
    ∃ b : Bool,∃ c : AlgebraicComplex,c≠0 ∧
      sourceKBasis.symm.action f=purePin c (!b) 1 := by
  let g := sourceKBasis.symm.action f
  have hg : g≠0 := by
    intro hz
    apply hf
    have he := congrArg sourceKBasis.action hz
    change sourceKBasis.action (sourceKBasis.symm.action f)=sourceKBasis.action 0 at he
    rw [InvertibleKernel.action_symm_action] at he
    exact he.trans (Signature.coordinateAction_zero _)
  have hp : g (fun _ => false)*g (fun _ => true)=0 := by
    rw [pairing_diagnostic] at hiso
    change g (fun _ => false)*g (fun _ => true)+g (fun _ => true)*g (fun _ => false)=0 at hiso
    have ht : (2 : AlgebraicComplex)*(g (fun _ => false)*g (fun _ => true))=0 := by
      linear_combination hiso
    exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
  have hnz : g (fun _ => false)≠0 ∨ g (fun _ => true)≠0 := by
    by_contra h
    push Not at h
    apply hg
    funext x
    rw [unary_word x]
    cases x 0
    · exact h.1
    · exact h.2
  rcases hnz with h0|h1
  · have h1 := (mul_eq_zero.mp hp).resolve_left h0
    refine ⟨true,g (fun _ => false),h0,?_⟩
    funext x
    rw [unary_word x]
    cases x 0 <;> simp [g,purePin,funext_iff] at h1 ⊢
    exact h1
  · have h0 := (mul_eq_zero.mp hp).resolve_right h1
    refine ⟨false,g (fun _ => true),h1,?_⟩
    funext x
    rw [unary_word x]
    cases x 0 <;> simp [g,purePin,funext_iff] at h0 ⊢
    exact h0

/-- The actual original opposite support supplies the new independent unary.
Only original rows appear in the returned graph; K contributes no vertex. -/
theorem escape (F : SignatureFamily AlgebraicComplex)
    (U : Network AlgebraicComplex 1) (hUF : Uses U F) (hUE : Ordinary U)
    (c : AlgebraicComplex) (hc : c≠0) (b : Bool)
    (hU : sourceKBasis.symm.action U.denote=purePin c (!b) 1)
    (g : AnySignature AlgebraicComplex) (hg : g∈kCoordinates F)
    (x : Fin g.1 → Bool) (hx : g.2 x≠0) (hpos : 0<balance b x) :
    ∃ k : ℕ,k+1≤g.1 ∧ ((k+1 : ℕ) : ℤ)=balance b x ∧
      ∃ V : Network AlgebraicComplex 1,Uses V F ∧ Ordinary V ∧
        pairing U.denote V.denote≠0 ∧ V.shape.vertices=k*U.shape.vertices+1 := by
  obtain ⟨k,hkn,hcharge,V,hVF,hVX,hVb,hVv⟩ := GeneralOddUnaryEscape.escape
    (kCoordinates F) (by norm_num) (toNative U) (toNative_uses F U hUF)
    (toNative_native U hUE) c hc b (by rw [toNative_denote]; exact hU)
    g.2 hg x hx hpos
  refine ⟨k,hkn,hcharge,toOrdinary V,toOrdinary_uses F V hVF,
    toOrdinary_ordinary V hVX,?_,hVv⟩
  rw [pairing_diagnostic,toOrdinary_denote,InvertibleKernel.symm_action_action,hU]
  cases b <;> simp [purePin,funext_iff] at hVb ⊢ <;> exact ⟨hc,hVb⟩

/-- Both support signs are obtained from failure of the common-side predicate;
neither a selected opposite row nor the new independent unary is an input. -/
theorem escape_isotropic (F : SignatureFamily AlgebraicComplex)
    (U : Network AlgebraicComplex 1) (hUF : Uses U F) (hUE : Ordinary U)
    (hnz : U.denote≠0) (hiso : pairing U.denote U.denote=0)
    (hside : ¬CommonOneSided (kCoordinates F)) :
    ∃ V : Network AlgebraicComplex 1,Uses V F ∧ Ordinary V ∧
      pairing U.denote V.denote≠0 := by
  obtain ⟨b,c,hc,hU⟩ := isotropic_diagnostic U.denote hnz hiso
  have hboth := (commonOneSided_or_bothChargeSigns (kCoordinates F)).resolve_left hside
  obtain ⟨g,hg,x,hx,hpos⟩ : ∃g∈kCoordinates F,∃x,g.2 x≠0 ∧ 0<balance b x := by
    cases b
    · obtain ⟨g,hg,x,hx,hneg⟩ := hboth.1
      refine ⟨g,hg,x,hx,?_⟩
      rw [balance_false]
      omega
    · obtain ⟨g,hg,x,hx,hpos⟩ := hboth.2
      exact ⟨g,hg,x,hx,by rwa [balance_true]⟩
  obtain ⟨k,_,_,V,hVF,hVE,hpair,_⟩ := escape F U hUF hUE c hc b hU g hg x hx hpos
  exact ⟨V,hVF,hVE,hpair⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnaryOrdinary
