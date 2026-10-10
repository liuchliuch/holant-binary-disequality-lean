import Holant.ReedMuller.TwoChart.ContextRealization

/-! Phase-free companion: genuinely Flat contexts require only the literal
RM, I, and X resources from the frozen native flat-network converse. No phase
Bell tensor is added. Native X subdivision retains actual I/X occurrences. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n m p : ℕ}

theorem algebraicBell_I : algebraicBell 0 0=
    (fun x : Word 2 => Signature.equality (x 0) (x 1)) := by
  funext x
  apply Subtype.ext
  change bellSignature 0 0 x=(((Signature.equality (x 0) (x 1)):AlgebraicComplex):ℂ)
  rw [PhaseNetwork.bell_zero_zero]
  dsimp only
  cases x 0 <;> cases x 1 <;> rfl

theorem algebraicBell_X : algebraicBell 1 0=
    (fun x : Word 2 => Signature.disequality (x 0) (x 1)) := by
  funext x
  apply Subtype.ext
  change bellSignature 1 0 x=(((Signature.disequality (x 0) (x 1)):AlgebraicComplex):ℂ)
  rw [PhaseNetwork.bell_one_zero]
  dsimp only
  cases x 0 <;> cases x 1 <;> rfl

/-- Exactly the literal I, X, and RM signatures; no phase resources. -/
def algebraicNativeFamily : SignatureFamily AlgebraicComplex := {f |
  f=⟨2,fun x => Signature.equality (x 0) (x 1)⟩ ∨
  f=⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ ∨ f=⟨8,algebraicRM⟩}

theorem algebraicNative_iff (f : AnySignature AlgebraicComplex) :
    f∈algebraicNativeFamily ↔ complexSignature f∈GenerationNetwork.nativeFamily := by
  have hi : complexSignature ⟨2,algebraicBell 0 0⟩=
      ⟨2,fun x => Signature.equality (x 0) (x 1)⟩ := by
    change (⟨2,bellSignature 0 0⟩ : AnySignature ℂ)=_
    rw [PhaseNetwork.bell_zero_zero]
  have hx : complexSignature ⟨2,algebraicBell 1 0⟩=
      ⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ := by
    change (⟨2,bellSignature 1 0⟩ : AnySignature ℂ)=_
    rw [PhaseNetwork.bell_one_zero]
  change (f=⟨2,_⟩ ∨ f=⟨2,_⟩ ∨ f=⟨8,_⟩) ↔ _
  rw [←algebraicBell_I,←algebraicBell_X]
  constructor
  · rintro (rfl|rfl|rfl)
    · exact Or.inl hi
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr rfl)
  · rintro (hi'|hx'|hr)
    · exact Or.inl (complexSignature_injective (hi'.trans hi.symm))
    · exact Or.inr (Or.inl (complexSignature_injective (hx'.trans hx.symm)))
    · exact Or.inr (Or.inr (complexSignature_injective hr))

theorem native_family_algebraic (f : AnySignature ℂ)
    (hf : f∈GenerationNetwork.nativeFamily) : ∀x,f.2 x∈AlgebraicComplex := by
  apply retained_algebraic (fun _ _ => 1) f
  have hh := PhaseNetwork.nativeFamily_subset_literal hf
  rcases hh with hr|⟨d,l,hb⟩
  · exact Or.inl hr
  · exact Or.inr ⟨d,l,by simpa only [OneMemClass.coe_one,one_smul] using hb⟩

theorem flat_shiftWord (f : Signature ℂ n) (hf : Flat f) (t : BinaryVector n) :
    Flat (fun x => f (GenerationNetwork.shiftWord t x)) := by
  obtain ⟨c,a,D,hD,rfl⟩ := hf
  refine ⟨c,a+t,D,hD,?_⟩
  funext x
  change (if vectorWord (GenerationNetwork.shiftWord t x)-a∈D then (c:ℂ) else 0)=
    (if vectorWord x-(a+t)∈D then (c:ℂ) else 0)
  rw [GenerationNetwork.vector_shiftWord]
  have hs : vectorWord x-t-a=vectorWord x-(a+t) := by abel
  rw [hs]

theorem flat_complementInputs (f : Signature ℂ (n+m)) (hf : Flat f) :
    Flat (fun x => f (complementInputs (n:=n) (m:=m) x)) := flat_shiftWord f hf _

/-- The fixed phase-free source converse, lifted without changing any
coefficient, ordered port, or graph incidence. -/
theorem algebraic_flat_network_converse
    (k : ℕ) (hp : p=2*k) (C : Signature AlgebraicComplex p)
    (hf : Flat (fun x => (C x:ℂ))) :
    ∃(R : Network AlgebraicComplex p) (s : AlgebraicComplex),s≠0 ∧
      (∀v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature AlgebraicComplex)∈algebraicNativeFamily) ∧
      (∀e,R.edge e=Signature.disequality) ∧ (∀x,R.denote x=s*C x) ∧
      R.shape.vertices≤20*k^2+5*k ∧ R.shape.edges≤32*k^2+4*k := by
  subst p
  have hCc := nonzeroFlat_nonzero _ (flat_is_nonzeroFlat _ hf)
  have hC : C≠0 := by
    intro hz
    apply hCc
    simp only [hz,Pi.zero_apply,ZeroMemClass.coe_zero]
    rfl
  obtain ⟨c,a,D,hD,hCf⟩ := hf
  obtain ⟨N,hv,he,hd,_,hvs,hes⟩ := source_flat_network_native k a D hD
  let hV := fun v => native_family_algebraic ⟨N.shape.arity v,N.vertex v⟩ (hv v)
  let hE := native_edges_algebraic N he
  let R := algebraicLift N hV hE
  have hRd : ∀x,(R.denote x:ℂ)=(c:ℂ)⁻¹*(C x:ℂ) := by
    intro x
    rw [algebraicLift_denote,hd]
    have hh := congrFun hCf x
    rw [hh]
    unfold flatSignature
    split_ifs
    · simp [c.ne_zero]
    · simp
  obtain ⟨s,hs,_,hds⟩ :=
    algebraic_network_scalar R C hC (c:ℂ)⁻¹ (inv_ne_zero c.ne_zero) hRd
  refine ⟨R,s,hs,?_,algebraicLift_native N hV hE he,hds,hvs,hes⟩
  intro v
  apply (algebraicNative_iff _).mpr
  exact hv v

/-- One original input occurrence, genuine phase-free Flat context, only
literal RM/I/X resources, native X gluing, and explicit quadratic bounds. -/
theorem one_copy_flat_context_realization
    (k : ℕ) (hnm : n+m=2*k) (g : Signature AlgebraicComplex n)
    (C : Signature AlgebraicComplex (n+m))
    (hf : Flat (fun x => (C x:ℂ))) :
    ∃(N : Network AlgebraicComplex m) (s : AlgebraicComplex),s≠0 ∧
      OneInputOccurrence algebraicNativeFamily g N ∧
      (∀e,N.edge e=Signature.disequality) ∧
      (∀b,N.denote b=s*∑x : Word n,g x*C (Fin.addCases x b)) ∧
      N.shape.vertices≤1+(20*k^2+5*k) ∧ N.shape.edges≤32*k^2+4*k+n := by
  let C' : Signature AlgebraicComplex (n+m) := fun x => C (complementInputs (n:=n) (m:=m) x)
  have hf' : Flat (fun x => (C' x:ℂ)) := flat_complementInputs _ hf
  obtain ⟨R,s,hs,hv,he,hd,hvs,hes⟩ := algebraic_flat_network_converse k hnm C' hf'
  refine ⟨NetworkPlug.withInput g R,s,hs,
    withInput_oneOccurrence _ g R hv,NetworkPlug.withInput_native g R he,
    withInput_complement_denote g C R s hd,?_,?_⟩
  · rw [NetworkPlug.withInput_vertices]
    omega
  · rw [NetworkPlug.withInput_edges]
    omega

end
end Holant.ReedMuller.TwoChart
