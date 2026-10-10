import Holant.ReedMuller.TwoChart.ContextRealizationComplement

/-! Actual algebraic one-copy contexts. The retained resources have their
fixed supplied Bell scalars, every physical edge is X, and precisely one
distinguished vertex carries the original input signature in its original
port order. The overall nonzero scalar is an algebraic coefficient quotient. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n m p : ℕ}

/-- The literal retained RM tensor, interpreted in the algebraic field. -/
def algebraicRM : Signature AlgebraicComplex 8 := fun x => ⟨rmCore x,rm_algebraic x⟩

/-- The literal ordered Bell tensor, interpreted in the algebraic field. -/
def algebraicBell (d l : ZMod 2) : Signature AlgebraicComplex 2 :=
  fun x => ⟨bellSignature d l x,bell_algebraic d l x⟩

/-- Exactly RM and the four supplied actual Bell representatives. This
family includes no closure under port permutations or scalar multiplication. -/
def algebraicRetainedFamily (κ : ZMod 2→ZMod 2→AlgebraicComplex) :
    SignatureFamily AlgebraicComplex :=
  {f | f=⟨8,algebraicRM⟩ ∨ ∃ d l,f=⟨2,κ d l • algebraicBell d l⟩}

def complexSignature (f : AnySignature AlgebraicComplex) : AnySignature ℂ :=
  ⟨f.1,fun x => (f.2 x:ℂ)⟩

theorem complexSignature_injective : Function.Injective complexSignature := by
  rintro ⟨a,f⟩ ⟨b,g⟩ h
  have hab : a=b := congrArg Sigma.fst h
  subst b
  have hfg : (fun x => (f x:ℂ))=(fun x => (g x:ℂ)) := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  congr 1
  funext x
  exact Subtype.ext (congrFun hfg x)

theorem algebraicRetained_iff (κ : ZMod 2→ZMod 2→AlgebraicComplex)
    (f : AnySignature AlgebraicComplex) :
    f∈algebraicRetainedFamily κ ↔
      complexSignature f∈retainedFamily (fun d l => (κ d l:ℂ)) := by
  constructor
  · rintro (rfl|⟨d,l,rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨d,l,rfl⟩
  · rintro (hr|⟨d,l,hb⟩)
    · exact Or.inl (complexSignature_injective hr)
    · exact Or.inr ⟨d,l,complexSignature_injective hb⟩

/-- An algebraic supported coefficient determines the actual projective
scalar, even when the source converse originally returns a complex scalar. -/
theorem algebraic_network_scalar (M : Network AlgebraicComplex p)
    (C : Signature AlgebraicComplex p) (hC : C≠0) (c : ℂ) (hc : c≠0)
    (hd : ∀x,(M.denote x:ℂ)=c*(C x:ℂ)) :
    ∃s : AlgebraicComplex,s≠0 ∧ (s:ℂ)=c ∧ ∀x,M.denote x=s*C x := by
  have hex : ∃x,C x≠0 := by
    by_contra! h
    exact hC (funext h)
  obtain ⟨x,hx⟩ := hex
  let s : AlgebraicComplex := M.denote x/C x
  have hxc : (C x:ℂ)≠0 := by exact_mod_cast hx
  have hsc : (s:ℂ)=c := by
    change (M.denote x:ℂ)/(C x:ℂ)=c
    exact (div_eq_iff hxc).mpr (hd x)
  refine ⟨s,?_,hsc,?_⟩
  · intro hz
    apply hc
    simpa only [hz,ZeroMemClass.coe_zero] using hsc.symm
  · intro y
    apply Subtype.ext
    change (M.denote y:ℂ)=(s:ℂ)*(C y:ℂ)
    rw [hsc,hd]

theorem algebraicLift_native (N : Network ℂ p)
    (hv : ∀v x,N.vertex v x∈AlgebraicComplex)
    (he : ∀e a b,N.edge e a b∈AlgebraicComplex)
    (hn : ∀e,N.edge e=Signature.disequality) :
    ∀e,(algebraicLift N hv he).edge e=Signature.disequality := by
  intro e
  funext a b
  apply Subtype.ext
  change N.edge e a b=(((Signature.disequality a b):AlgebraicComplex):ℂ)
  rw [hn]
  cases a <;> cases b <;> rfl

/-- The source's RM/Bell converse with actual algebraic coefficients and an
actual nonzero algebraic scalar; the graph is preserved by coefficient lift. -/
theorem algebraic_character_network_converse
    (κ : ZMod 2→ZMod 2→AlgebraicComplex) (hκ : ∀d l,κ d l≠0)
    (k : ℕ) (hp : p=2*k) (C : Signature AlgebraicComplex p)
    (hf : CFlat (fun x => (C x:ℂ))) (hC : C≠0) :
    ∃(R : Network AlgebraicComplex p) (s : AlgebraicComplex),s≠0 ∧
      (∀v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature AlgebraicComplex)∈algebraicRetainedFamily κ) ∧
      (∀e,R.edge e=Signature.disequality) ∧ (∀x,R.denote x=s*C x) ∧
      R.shape.vertices≤20*k^2+7*k ∧ R.shape.edges≤32*k^2+6*k := by
  subst p
  have hκc : ∀d l,(κ d l:ℂ)≠0 := by intro d l;exact_mod_cast hκ d l
  have hCc : (fun x => (C x:ℂ))≠0 := by
    intro hz
    apply hC
    funext x
    exact Subtype.ext (congrFun hz x)
  obtain ⟨N,c,hc,hv,he,hd,_,hvs,hes⟩ :=
    source_character_network_converse_of_CFlat _ hκc k _ hf hCc
  let hV := fun v => retained_algebraic κ ⟨N.shape.arity v,N.vertex v⟩ (hv v)
  let hE := native_edges_algebraic N he
  let R := algebraicLift N hV hE
  have hRd : ∀x,(R.denote x:ℂ)=c*(C x:ℂ) := by
    intro x
    rw [algebraicLift_denote,hd]
    rfl
  obtain ⟨s,hs,_,hds⟩ := algebraic_network_scalar R C hC c hc hRd
  refine ⟨R,s,hs,?_,algebraicLift_native N hV hE he,hds,hvs,hes⟩
  intro v
  apply (algebraicRetained_iff κ _).mpr
  exact hv v

/-- A distinguished physical occurrence carries g; every other occurrence
belongs to A. A retained tensor may happen to equal g, so occurrence identity
rather than label inequality is the meaningful one-copy guarantee. -/
def OneInputOccurrence {K : Type*} (A : SignatureFamily K) (g : Signature K n)
    (N : Network K m) : Prop :=
  ∃v : Fin N.shape.vertices,
    (⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)=⟨n,g⟩ ∧
    ∀w,w≠v → (⟨N.shape.arity w,N.vertex w⟩ : AnySignature K)∈A

theorem OneInputOccurrence.vertex_mem {K : Type*} {A : SignatureFamily K}
    {g : Signature K n} {N : Network K m} (hN : OneInputOccurrence A g N) :
    ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈insert (⟨n,g⟩ : AnySignature K) A := by
  obtain ⟨v,hv,hothers⟩ := hN
  intro w
  by_cases hw : w=v
  · subst w
    rw [hv]
    exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (hothers w hw)

theorem OneInputOccurrence.realizes {K : Type*} [CommSemiring K]
    {A : SignatureFamily K} {g : Signature K n} {N : Network K m}
    (hN : OneInputOccurrence A g N) (he : ∀e,N.edge e=Signature.disequality) :
    Gadget.Realizes (insert (⟨n,g⟩ : AnySignature K) A) .disequality N.denote :=
  Gadget.realizes_network N _ .disequality hN.vertex_mem he

theorem withInput_oneOccurrence {K : Type*} [CommSemiring K]
    (A : SignatureFamily K) (g : Signature K n) (R : Network K (n+m))
    (hR : ∀v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature K)∈A) :
    OneInputOccurrence A g (NetworkPlug.withInput g R) := by
  let L := Certificates.FourthRootOdd.singleVertexNetwork g
  let E := Fintype.equivFin (Fin 1⊕Fin R.shape.vertices)
  refine ⟨E (.inl 0),?_,?_⟩
  · change (⟨(NetworkPlug.finite L R (fun _ => Signature.disequality)).arity (E.symm (E (.inl 0))),
      (NetworkPlug.finite L R (fun _ => Signature.disequality)).vertex (E.symm (E (.inl 0)))⟩ : AnySignature K)=_
    rw [E.symm_apply_apply]
    rfl
  · intro w hw
    change (⟨(NetworkPlug.finite L R (fun _ => Signature.disequality)).arity (E.symm w),
      (NetworkPlug.finite L R (fun _ => Signature.disequality)).vertex (E.symm w)⟩ : AnySignature K)∈A
    cases hh : E.symm w with
    | inl u =>
      have hu : u=0 := Subsingleton.elim _ _
      subst u
      have hw' : w=E (.inl 0) := by simpa using congrArg E hh
      exact (hw hw').elim
    | inr v => exact hR v

/-- The actual one-copy physical context for an algebraic nonzero CFlat
relation. Original input labels and output order are literal; the context's
input complement precisely cancels native-X gluing. -/
theorem one_copy_context_realization
    (κ : ZMod 2→ZMod 2→AlgebraicComplex) (hκ : ∀d l,κ d l≠0)
    (k : ℕ) (hnm : n+m=2*k) (g : Signature AlgebraicComplex n)
    (C : Signature AlgebraicComplex (n+m))
    (hf : CFlat (fun x => (C x:ℂ))) (hC : C≠0) :
    ∃(N : Network AlgebraicComplex m) (s : AlgebraicComplex),s≠0 ∧
      OneInputOccurrence (algebraicRetainedFamily κ) g N ∧
      (∀e,N.edge e=Signature.disequality) ∧
      (∀b,N.denote b=s*∑x : Word n,g x*C (Fin.addCases x b)) ∧
      N.shape.vertices≤1+(20*k^2+7*k) ∧ N.shape.edges≤32*k^2+6*k+n := by
  let C' : Signature AlgebraicComplex (n+m) := fun x => C (complementInputs (n:=n) (m:=m) x)
  have hf' : CFlat (fun x => (C' x:ℂ)) := CFlat_complementInputs _ hf
  have hC' : C'≠0 := by
    intro hz
    apply hC
    funext x
    have hh := congrFun hz (complementInputs (n:=n) (m:=m) x)
    simpa only [C',complementInputs_involutive,Pi.zero_apply] using hh
  obtain ⟨R,s,hs,hv,he,hd,hvs,hes⟩ :=
    algebraic_character_network_converse κ hκ k hnm C' hf' hC'
  refine ⟨NetworkPlug.withInput g R,s,hs,
    withInput_oneOccurrence _ g R hv,NetworkPlug.withInput_native g R he,
    withInput_complement_denote g C R s hd,?_,?_⟩
  · rw [NetworkPlug.withInput_vertices]
    omega
  · rw [NetworkPlug.withInput_edges]
    omega

end
end Holant.ReedMuller.TwoChart
