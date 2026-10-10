import Holant.Proofs.Algorithms.QuaternaryAnchorAccess
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Proofs.Algorithms.RawArityTransport
import Holant.Complexity.UniversalPairReduction.BinaryInsertion
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Preparation
import Holant.Complexity.EdgeSubdivision.VertexSubstitution
import Holant.NetworkContraction


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.MainChain.QuaternaryOrdinaryCompanion
open Computability Holant.Algebraic Holant.Complexity Holant.Tractable
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open UniversalPairReduction
open SmoothingCompiler
open Holant.EightVertex.ProductAnchor
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

section Ordinary
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {a : ℕ → ℕ}
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (a i.val))

def tables : ExactSignatureTables d s 1 a where
  vertex i x := F.decode.symm (G i x)
  edge _ b c := F.decode.symm (Signature.equality b c)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev targetValue := (tables F G).evaluate F

/-- Only the generic validated incidence/occurrence type is reused. The
network below has Eq edges; no native-X value or smoothing theorem is cast. -/
def network (B : BinaryTable K) (r : UniversalPairReduction.Input s a) : Network K 0 :=
  r.val.realize r.property.1 (BinaryFamily.signatures G B) (fun _ : Fin 1 => Signature.equality)
def value (B : BinaryTable K) (r : UniversalPairReduction.Input s a) : K :=
  (network G B r).denote Fin.elim0

private theorem transportSignature_heq {m n : ℕ} (h : m=n) (f : Signature K m) :
    HEq (fun x : Fin n → Bool => f (fun i => x (Fin.cast h i))) f := by
  subst n
  rfl

/-- The two existing closed-port maps remove only the impossible boundary
summand. They preserve the very same ordered edge-end occurrence. -/
private theorem closed_port_eq (S : NetworkShape 0)
    (p : Σ v : Fin S.vertices, Fin (S.arity v)) :
    S.closedPorts p=ClosedLabelling.closedPortEquiv S p := by
  cases hp : S.ports p with
  | inl i => exact Fin.elim0 i
  | inr e =>
    simp [NetworkShape.closedPorts,ClosedLabelling.closedPortEquiv,
      RawClosedNetwork.closedEndsEquiv,hp]

/-- Literal old-label branch of the original binary table. Its dependent
arity cast is only a proof transport; the signature and its ports stay G i. -/
private theorem old_signature_heq (B : BinaryTable K) (i : Fin (s+1)) (hi : i.val<s) :
    HEq (BinaryFamily.signatures G B i) (G ⟨i.val,hi⟩) := by
  have hd : a i.val=extendedArity s a i.val := by simp [extendedArity,hi]
  have hs : BinaryFamily.signatures G B i=
      (fun x : Fin (extendedArity s a i.val) → Bool =>
        G ⟨i.val,hi⟩ (fun k => x (Fin.cast hd k))) := by
    funext x
    simp only [BinaryFamily.signatures,dite_eq_left hi] <;> rfl
  exact (heq_of_eq hs).trans (transportSignature_heq hd (G ⟨i.val,hi⟩))

structure Marked where
  input : UniversalPairReduction.Input s a
  vertex : Fin input.val.vertices.length
  label : (input.val.vertices.get vertex).1=s

def markedArity (w : Marked (s:=s) (a:=a)) :
    (network G 0 w.input).shape.arity w.vertex=2 := by
  change extendedArity s a (w.input.val.vertices.get w.vertex).1=2
  rw [w.label]
  simp [extendedArity]
def hole (w : Marked (s:=s) (a:=a)) : BinaryTable K :=
  binaryRaw (network G 0 w.input) w.vertex (markedArity G w)

theorem insert_value (w : Marked (s:=s) (a:=a)) (B : BinaryTable K) :
    value G B w.input=(hole G w).insert B := by
  have ho : ∀u,u≠w.vertex → (network G 0 w.input).vertex u=(network G B w.input).vertex u := by
    intro u hu
    exact BinaryFamily.vertex_old_eq G 0 B w.input w.vertex w.label u hu
  have h := denote_binary_relabel (w.input.val.shape w.input.property.1)
    (network G 0 w.input).vertex (network G B w.input).vertex
    (fun _ => Signature.equality) w.vertex (markedArity G w) ho
  refine h.trans ?_
  congr 1
  funext b c
  exact BinaryFamily.vertex_new G B w.input w.vertex w.label b c

theorem absent_value (r : UniversalPairReduction.Input s a)
    (h : occurrences s r.val=0) (B C : BinaryTable K) : value G B r=value G C r := by
  unfold value network
  refine congrFun (Network.denote_congr _ _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x
    have hv := (r.property.1.1 v).1
    have hn := absent_label s h _ (List.get_mem _ v)
    have hl : (r.val.vertices.get v).1<s := by omega
    have hl' : r.val.vertices[v.val].1<s := by simpa using hl
    simp [RawClosedNetwork.realize,RawClosedNetwork.signatureLabel,BinaryFamily.signatures,hl']
  · intro e b c
    rfl

theorem marked_exists (r : UniversalPairReduction.Input s a)
    (h : occurrences s r.val≠0) : ∃w : Marked (s:=s) (a:=a),w.input=r := by
  have hm : ∃row∈r.val.vertices,row.1=s := by
    by_contra! hn
    apply h
    simp only [occurrences,List.length_eq_zero_iff,List.filter_eq_nil_iff]
    intro row hr
    simpa using hn row hr
  obtain ⟨row,hr,hl⟩ := hm
  obtain ⟨v,hv⟩ := List.mem_iff_get.mp hr
  exact ⟨⟨r,v,(congrArg Prod.fst hv).trans hl⟩,rfl⟩

variable (j4 : Fin s)
variable (h4 : (⟨a j4.val,G j4⟩ : AnySignature K)=⟨4,equalityFour⟩)

/-- Actual ordinary Eq2: close original ports 0,1 of one supplied Eq4;
its remaining ordered ports are 2,3. The contraction scalar is exactly one. -/
def equalityNetwork : Network K 2 := (Network.corolla equalityFour).contract Signature.equality
def equalityLabels : Labelling (equalityNetwork (K:=K)).shape s 1 a where
  vertex _ := j4
  vertex_arity _ := congrArg Sigma.fst h4
  edge _ := 0
theorem equality_tensor : (equalityNetwork (K:=K)).denote=fun x => Signature.equality (x 0) (x 1) := by
  rw [equalityNetwork,Network.denote_contract,Network.denote_corolla]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Signature.contract,Signature.equality,equalityFour,Fintype.sum_bool,
      Fin.forall_fin_succ,h0,h1]

theorem equality_labels_tensor :
    ((equalityLabels G j4 h4).sourceNetwork G (fun _ : Fin 1 => Signature.equality)).denote=
      fun x => Signature.equality (x 0) (x 1) := by
  rw [←equality_tensor]
  apply Network.denote_congr
  · intro v x
    exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (G j4) equalityFour h4 (congrArg Sigma.fst h4) x
  · intro e b c
    fin_cases e
    rfl

namespace DiagonalContext
variable (w : Marked (s:=s) (a:=a))
abbrev N := network G 0 w.input
abbrev Others := DeleteVertex.Vertices (N G w) w.vertex
abbrev V := Unit ⊕ Others G w
abbrev arity : V G w → ℕ := Sum.elim (fun _ => 4) (fun u => (N G w).shape.arity u.val)

/-- Original marked ports become the first two Eq4 ports. Its last two
ports are the new ordered boundary. All original edges are kept, even when
the two marked occurrences are opposite ends of the SAME self-loop. -/
def regroup {P : Type} : ((Fin 2 ⊕ Fin 2) ⊕ P) ≃ (Fin 2 ⊕ (Fin 2 ⊕ P)) where
  toFun | .inl (.inl i) => .inr (.inl i)
        | .inl (.inr i) => .inl i
        | .inr p => .inr (.inr p)
  invFun | .inl i => .inl (.inr i)
         | .inr (.inl i) => .inl (.inl i)
         | .inr (.inr p) => .inr p
  left_inv := by rintro ((i|i)|p) <;> rfl
  right_inv := by rintro (i|(i|p)) <;> rfl

def ports : (Σv : V G w,Fin (arity G w v)) ≃
    (Fin 2 ⊕ (Fin (N G w).shape.edges×Bool)) :=
  (Equiv.sumSigmaDistrib (fun v => Fin (arity G w v))).trans
    ((Equiv.sumCongr ((Equiv.uniqueSigma (fun _ : Unit => Fin 4)).trans
      (finSumFinEquiv (m:=2) (n:=2)).symm) (Equiv.refl _)).trans
      ((regroup).trans (Equiv.sumCongr (Equiv.refl _)
        ((Equiv.sumComm _ _).trans
          ((DeleteVertex.portEquiv (N G w) w.vertex (markedArity G w)).symm.trans
            (ClosedLabelling.closedPortEquiv (N G w).shape))))))

abbrev finite : Holant.FiniteNetwork K (V G w) (Fin (N G w).shape.edges) 2 where
  arity := arity G w
  ports := ports G w
  vertex | .inl _ => equalityFour
         | .inr u => (N G w).vertex u.val
  edge := (N G w).edge
abbrev graph := (finite G w).toNetwork

theorem boundary_value (x : Fin 2 → Bool) :
    (graph G w).denote x=if x 0=x 1 then hole G w (x 0) (x 1) else 0 := by
  rw [graph,Holant.FiniteNetwork.denote_toNetwork]
  unfold Holant.FiniteNetwork.denote hole binaryRaw rawHole
  let H : ((Fin (N G w).shape.edges × Bool) → Bool) → K := fun z =>
    if (N G w).shape.assignment Fin.elim0 z w.vertex =
        (fun i => (![x 0,x 1] : Fin 2 → Bool) (Fin.cast (markedArity G w) i))
    then holeWeight (N G w) w.vertex z else 0
  have hs : (if x 0=x 1 then ∑ z,H z else 0) =
      ∑ z,if x 0=x 1 then H z else 0 := by
    by_cases hx : x 0=x 1 <;> simp [hx]
  change _ = if x 0=x 1 then ∑ z,H z else 0
  rw [hs]
  dsimp only [H]
  refine Finset.sum_congr (by ext z; simp) ?_
  intro z _
  simp only [finite,Fintype.prod_sum_type,Fintype.prod_unique]
  have hold : (∏u : Others G w,(N G w).vertex u.val
      (fun k => Sum.elim x z (ports G w ⟨.inr u,k⟩)))=
      ∏u∈Finset.univ.erase w.vertex,(N G w).vertex u ((N G w).shape.assignment Fin.elim0 z u) := by
    rw [Finset.prod_subtype (p:=fun u => u≠w.vertex) (Finset.univ.erase w.vertex) (by simp)]
    apply Finset.prod_congr rfl
    intro u _
    congr 1 <;> (funext k; simp [ports,regroup,DeleteVertex.port_other,NetworkShape.assignment,
      ClosedLabelling.closedPortEquiv])
  erw [hold]
  have hxword : (![x 0,x 1] : Fin 2 → Bool)=x := by
    funext i
    fin_cases i <;> rfl
  have hassign : (N G w).shape.assignment Fin.elim0 z w.vertex=
      (fun k => (![x 0,x 1] : Fin 2 → Bool) (Fin.cast (markedArity G w) k)) ↔
      (∀i : Fin 2,z (ClosedLabelling.closedPortEquiv (N G w).shape
        ⟨w.vertex,Fin.cast (markedArity G w).symm i⟩)=x i) := by
    constructor
    · intro h i
      have hi := congrFun h (Fin.cast (markedArity G w).symm i)
      rw [ClosedLabelling.closed_assignment] at hi
      simpa only [closed_port_eq,hxword,Fin.cast_cast,Fin.cast_eq_self] using hi
    · intro h
      funext k
      rw [ClosedLabelling.closed_assignment]
      simpa only [closed_port_eq,hxword,Fin.cast_cast,Fin.cast_eq_self] using
        h (Fin.cast (markedArity G w) k)
  have hdel (i : Fin 2) : (DeleteVertex.portEquiv (N G w) w.vertex (markedArity G w)).symm (.inr i) =
      ⟨w.vertex,Fin.cast (markedArity G w).symm i⟩ := by
    let e := DeleteVertex.portEquiv (N G w) w.vertex (markedArity G w)
    calc e.symm (.inr i) = e.symm (e ⟨w.vertex,Fin.cast (markedArity G w).symm i⟩) :=
      congrArg e.symm (DeleteVertex.port_marked (N G w) w.vertex (markedArity G w) i).symm
      _ = _ := e.symm_apply_apply _
  simp only [hassign,holeWeight]
  generalize hz0 : z (ClosedLabelling.closedPortEquiv (N G w).shape
    ⟨w.vertex,Fin.cast (markedArity G w).symm 0⟩)=b
  generalize hz1 : z (ClosedLabelling.closedPortEquiv (N G w).shape
    ⟨w.vertex,Fin.cast (markedArity G w).symm 1⟩)=c
  cases b <;> cases c <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [ports,Equiv.sumSigmaDistrib,Equiv.uniqueSigma,finSumFinEquiv,Fin.addCases,regroup,equalityFour,Fin.forall_fin_succ,DeleteVertex.port_marked,hdel,
      hz0,hz1,h0,h1] <;> first | rfl | (left; rfl)

def labels : Labelling (graph G w).shape s 1 a where
  vertex v := match (Fintype.equivFin (V G w)).symm v with
    | .inl _ => j4
    | .inr u => ⟨(w.input.val.vertices.get u.val).1,
        BinaryFamily.other_label w.input w.vertex w.label u.val u.property⟩
  vertex_arity v := by
    change _ = arity G w ((Fintype.equivFin (V G w)).symm v)
    cases h : (Fintype.equivFin (V G w)).symm v with
    | inl t => simpa only [arity,Sum.elim_inl] using congrArg Sigma.fst h4
    | inr u =>
      change a (w.input.val.vertices.get u.val).1 =
        extendedArity s a (w.input.val.vertices.get u.val).1
      have hu := BinaryFamily.other_label w.input w.vertex w.label u.val u.property
      have hu' : w.input.val.vertices[u.val.val].1<s := by simpa using hu
      simp [extendedArity,hu']
  edge _ := 0

theorem labels_exact :
    ((labels G j4 h4 w).sourceNetwork G (fun _ : Fin 1 => Signature.equality)).denote=(graph G w).denote := by
  have hv : ∀v : Fin (graph G w).shape.vertices,
      (⟨a ((labels G j4 h4 w).vertex v).val,G ((labels G j4 h4 w).vertex v)⟩ : AnySignature K)=
        ⟨(graph G w).shape.arity v,(graph G w).vertex v⟩ := by
    intro v
    change (⟨a ((labels G j4 h4 w).vertex v).val,G ((labels G j4 h4 w).vertex v)⟩ : AnySignature K)=
      ⟨arity G w ((Fintype.equivFin (V G w)).symm v),
        (finite G w).vertex ((Fintype.equivFin (V G w)).symm v)⟩
    dsimp only [labels]
    cases h : (Fintype.equivFin (V G w)).symm v with
    | inl t => simpa [finite,arity,h] using h4
    | inr u =>
      have hu := BinaryFamily.other_label w.input w.vertex w.label u.val u.property
      simp only [finite,arity,h,Sum.elim_inr]
      apply Sigma.ext
      · change a (w.input.val.vertices.get u.val).1 =
          extendedArity s a (w.input.val.vertices.get u.val).1
        have hu' : w.input.val.vertices[u.val.val].1 < s := by simpa using hu
        simp [extendedArity,hu']
      · change HEq (G ⟨(w.input.val.vertices.get u.val).1,hu⟩)
          (BinaryFamily.signatures G 0
            (w.input.val.signatureLabel w.input.property.1 u.val))
        exact (old_signature_heq G 0
          (w.input.val.signatureLabel w.input.property.1 u.val) hu).symm
  apply Network.denote_congr
  · intro v x
    exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (G ((labels G j4 h4 w).vertex v)) ((graph G w).vertex v) (hv v)
      ((labels G j4 h4 w).vertex_arity v) x
  · intro e b c
    rfl
end DiagonalContext

/-- This quantifies concrete valid original-port contexts, not abstract
binary matrices. Failure produces an actual graph for diagonalization. -/
def HasGap (j : Bool) : Prop := ∃w : Marked (s:=s) (a:=a),hole G w j j≠hole G w (!j) (!j)
def witness (j : Bool) (h : HasGap G j) : Marked (s:=s) (a:=a) := Classical.choose h
theorem witness_gap (j : Bool) (h : HasGap G j) :
    hole G (witness G j h) j j≠hole G (witness G j h) (!j) (!j) := Classical.choose_spec h

def companion (j : Bool) : Bool → K := fun b => if b=j then (if HasGap G j then 1 else 2) else 0
def pair (j : Bool) : BinaryTable K := fun b c => (if b=j then 1 else 0)*companion G j c
theorem companion_nonzero (j : Bool) : companion G j j≠0 := by
  simp only [companion,ite_true]
  split_ifs <;> norm_num
theorem companion_algebraic (j b : Bool) : IsAlgebraic ℚ (companion G j b) := by
  unfold companion
  split_ifs
  · exact isAlgebraic_one
  · convert (isAlgebraic_one : IsAlgebraic ℚ (1 : K)).add isAlgebraic_one using 1 <;> norm_num
  · exact isAlgebraic_zero

/-- Keeping shape and its labels in one dependent pair prevents a proof
transport from obscuring the actual selected graph. No graph is changed. -/
def probeData (j : Bool) : Σ S : NetworkShape 2, Labelling S s 1 a :=
  if h : HasGap G j then
    ⟨(DiagonalContext.graph G (witness G j h)).shape,
      DiagonalContext.labels G j4 h4 (witness G j h)⟩
  else ⟨(equalityNetwork (K:=K)).shape,equalityLabels G j4 h4⟩
abbrev probeShape (j : Bool) : NetworkShape 2 := (probeData G j4 h4 j).1
abbrev probe (j : Bool) : Labelling (probeShape G j4 h4 j) s 1 a :=
  (probeData G j4 h4 j).2
def probeBinary (j : Bool) : BinaryTable K := fun b c =>
  ((probe G j4 h4 j).sourceNetwork G (fun _ : Fin 1 => Signature.equality)).denote ![b,c]
def alpha (j : Bool) : K := if h : HasGap G j then
  -hole G (witness G j h) (!j) (!j)/(hole G (witness G j h) j j-hole G (witness G j h) (!j) (!j)) else 1
def beta (j : Bool) : K := if h : HasGap G j then
  (hole G (witness G j h) j j-hole G (witness G j h) (!j) (!j))⁻¹ else 0

/-- Eq4 has physically diagonalized G1. Thus the b=0 subcase of the paper's
point-mass proof applies regardless of whether the original table also has
asymmetric G2 contexts. They are not assumed absent or discarded. -/
theorem reconstruction (j : Bool) (w : Marked (s:=s) (a:=a)) :
    (hole G w).insert (pair G j)=alpha G j*(hole G w).insert Signature.equality+
      beta G j*(hole G w).insert (probeBinary G j4 h4 j) := by
  by_cases h : HasGap G j
  · have hg := sub_ne_zero.mpr (witness_gap G j h)
    have hp : ∀b c,probeBinary G j4 h4 j b c=
        if b=c then hole G (witness G j h) b c else 0 := by
      intro b c
      simp only [probeBinary,probe,probeShape]
      rw [show probeData G j4 h4 j=
          ⟨(DiagonalContext.graph G (witness G j h)).shape,
            DiagonalContext.labels G j4 h4 (witness G j h)⟩ from dif_pos h]
      dsimp only
      rw [DiagonalContext.labels_exact,DiagonalContext.boundary_value]
      rfl
    cases j <;> simp [BinaryTable.insert,pair,companion,alpha,beta,h,hp,Signature.equality,sub_eq_add_neg] at hg ⊢
      <;> field_simp [hg] <;> ring
  · have hw : hole G w j j=hole G w (!j) (!j) := by
      by_contra hn
      exact h ⟨w,hn⟩
    cases j <;> simp [BinaryTable.insert,pair,companion,alpha,beta,h,Signature.equality] at *
      <;> linear_combination hw

section Queries
variable {S : NetworkShape 2} (L : Labelling S s 1 a)
def actualBinary : BinaryTable K := fun b c =>
  (L.sourceNetwork G (fun _ : Fin 1 => Signature.equality)).denote ![b,c]
def query (r : UniversalPairReduction.Input s a) := OrderedQueries.plus L (forget s a r)
def queryComputes := OrderedQueries.promisedComputes L (Equiv.refl _)

/-- The existing replacement compiler is kernel-parametric. This local
join proves its value for Eq edges and the literal B table on original
ports. It does not reuse QueryFamily's native-X semantic theorem. -/
theorem query_value (r : UniversalPairReduction.Input s a) :
    targetValue F G (query L r)=value G (actualBinary G L) r := by
  change (tables F G).evaluate F (query L r)=_
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [tables,LinearEquiv.apply_symm_apply]
  let τ := OrderedQueries.templates L (Equiv.refl _)
  have ha : sourceArity τ=extendedArity s a := OrderedQueries.arity_eq L (Equiv.refl _)
  have hw : ∀i<s+1,(τ i).WellFormed s 1 a := fun i hi =>
    (OrderedQueries.valid L (Equiv.refl _) i hi).1
  let cf : ExactSignatureTables.CoefficientIndex s 1 a → K := fun
    | .inl ⟨i,x⟩ => G i x
    | .inr (_,b,c) => Signature.equality b c
  have transport_heq : ∀{m n : ℕ} (h : m=n) (f : Signature K m),
      HEq (fun x : Fin n → Bool => f (fun i => x (Fin.cast h i))) f := by
    intro m n h f
    subst n
    rfl
  have hl : ∀i : Fin (s+1),((τ i.val).network (hw i.val i.isLt) G
      (fun _ : Fin 1 => Signature.equality)).denote=
      (fun x => BinaryFamily.signatures G (actualBinary G L) i
        (fun k => x (Fin.cast (congrFun ha i.val).symm k))) := by
    intro i
    have hh : HEq (((τ i.val).network (hw i.val i.isLt) G
        (fun _ : Fin 1 => Signature.equality)).denote)
        (BinaryFamily.signatures G (actualBinary G L) i) := by
      by_cases hi : i.val<s
      · have hold := OriginalFamily.ambientSource_old cf (permuteLabelling L (Equiv.refl _)).template
          (permuteLabelling L (Equiv.refl _)).wellFormed ⟨i.val,hi⟩
        have hb : HEq (BinaryFamily.signatures G (actualBinary G L) i) (G ⟨i.val,hi⟩) := by
          unfold BinaryFamily.signatures
          simp only [dif_pos hi]
          exact transport_heq (by simp [extendedArity,hi]) (G ⟨i.val,hi⟩)
        exact hold.trans hb.symm
      · have his : i.val=s := by omega
        have he : i=⟨s,Nat.lt_succ_self s⟩ := Fin.ext his
        subst i
        have hnew := OriginalFamily.ambientSource_new cf (permuteLabelling L (Equiv.refl _)).template
          (permuteLabelling L (Equiv.refl _)).wellFormed
        have hden : ((permuteLabelling L (Equiv.refl _)).template.network
            (permuteLabelling L (Equiv.refl _)).wellFormed G
            (fun _ : Fin 1 => Signature.equality)).denote=
            (L.sourceNetwork G (fun _ : Fin 1 => Signature.equality)).denote := by
          rw [Labelling.denote_template]
          funext x
          exact denote_permute L G (fun _ : Fin 1 => Signature.equality) (Equiv.refl _) x
        have hb : HEq (BinaryFamily.signatures G (actualBinary G L) ⟨s,Nat.lt_succ_self s⟩)
            (L.sourceNetwork G (fun _ : Fin 1 => Signature.equality)).denote := by
          unfold BinaryFamily.signatures
          simp only [dif_neg (Nat.lt_irrefl s)]
          have ht := transport_heq (show 2=extendedArity s a s by simp [extendedArity])
            (fun x : Fin 2 → Bool => actualBinary G L (x 0) (x 1))
          apply ht.trans
          apply heq_of_eq
          funext x
          dsimp only [actualBinary]
          congr 1
          funext k
          fin_cases k <;> rfl
        exact hnew.trans ((heq_of_eq hden).trans hb.symm)
    have hsigma : (⟨sourceArity τ i.val,((τ i.val).network (hw i.val i.isLt) G
          (fun _ : Fin 1 => Signature.equality)).denote⟩ : AnySignature K)=
        ⟨extendedArity s a i.val,BinaryFamily.signatures G (actualBinary G L) i⟩ :=
      Sigma.ext (congrFun ha i.val) hh
    funext x
    exact (Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (BinaryFamily.signatures G (actualBinary G L) i)
      ((τ i.val).network (hw i.val i.isLt) G (fun _ : Fin 1 => Signature.equality)).denote
      hsigma.symm (congrFun ha i.val).symm x).symm
  exact EdgeSubdivision.VertexSubstitution.partition τ ha hw r.val r.property.1
    (BinaryFamily.signatures G (actualBinary G L)) G (fun _ => Signature.equality) hl
end Queries

def queries (j : Bool) (r : UniversalPairReduction.Input s a) (b : Bool) :
    ExactSignatureTables.Input s 1 a :=
  if b then query (probe G j4 h4 j) r else query (equalityLabels G j4 h4) r
def queriesComputes (j b : Bool) : Computes (inputEncoding s a)
    (targetEncoding (s:=s) (a:=a)) (fun r => queries G j4 h4 j r b) := by
  cases b
  · exact queryComputes (equalityLabels G j4 h4)
  · exact queryComputes (probe G j4 h4 j)

def pre (j : Bool) (r : UniversalPairReduction.Input s a) :=
  ([queries G j4 h4 j r false,queries G j4 h4 j r true],decide (occurrences s r.val=1))
def preComputes (j : Bool) : Computes (inputEncoding s a)
    (OracleBatch.contextEncoding (targetEncoding (s:=s) (a:=a)) encodingBoolBool)
    (pre G j4 h4 j) :=
  pairComputes (Compiler.fixedListComputes (inputEncoding s a)
    (targetEncoding (s:=s) (a:=a)) (queries G j4 h4 j)
    (queriesComputes G j4 h4 j) [false,true]) (SmoothingCompiler.hasPairComputes s a)

def post (j : Bool) (p : List K×Bool) : K :=
  if p.2 then alpha G j*p.1.getD 0 0+beta G j*p.1.getD 1 0 else p.1.getD 0 0
def postComputes (j : Bool) : Computes (OracleBatch.contextEncoding F.encoding encodingBoolBool)
    F.encoding (post G j) := by
  let answers := Wiring.firstComputes (framedListEncoding F.encoding) encodingBoolBool
  let fst := answers.andThen (Compiler.getDComputes F.encoding 0 0)
  let snd := answers.andThen (Compiler.getDComputes F.encoding 1 0)
  let test := Wiring.secondComputes (framedListEncoding F.encoding) encodingBoolBool
  exact ifComputes test
    (congrComputes (addComputes F (scaleComputes F fst (alpha G j))
      (scaleComputes F snd (beta G j))) (fun p => by dsimp; ring)) fst

theorem recovery (j : Bool) (r : UniversalPairReduction.Input s a) :
    value G (pair G j) r=post G j (OracleBatch.answers (targetValue F G) (pre G j4 h4 j r)) := by
  have hS : targetValue F G (queries G j4 h4 j r false)=value G Signature.equality r := by
    change targetValue F G (query (equalityLabels G j4 h4) r)=_
    rw [query_value]
    congr 1
    funext b c
    exact congrFun (equality_labels_tensor G j4 h4) ![b,c]
  have hT : targetValue F G (queries G j4 h4 j r true)=value G (probeBinary G j4 h4 j) r :=
    query_value F G (probe G j4 h4 j) r
  by_cases hz : occurrences s r.val=0
  · have hn : occurrences s r.val≠1 := by omega
    simpa [pre,post,OracleBatch.answers,hn,hS] using
      absent_value G r hz (pair G j) Signature.equality
  · have ho : occurrences s r.val=1 := by have := r.property.2; omega
    obtain ⟨w,hw⟩ := marked_exists r hz
    subst r
    simpa [pre,post,OracleBatch.answers,ho,hS,hT,insert_value G w] using
      reconstruction G j4 h4 j w

/-- Real two-query transcript and field postprocessor. Both queries are
issued even when they coincide, so no repeated-call cost is hidden. -/
def controlled (j : Bool) : LengthControlledOracleReduction
    (inputEncoding s a) F.encoding (targetEncoding (s:=s) (a:=a)) F.encoding
    (value G (pair G j)) (targetValue F G) := by
  have he : value G (pair G j)=fun r =>
      post G j (OracleBatch.answers (targetValue F G) (pre G j4 h4 j r)) := funext (recovery F G j4 h4 j)
  rw [he]
  exact TraceQueryControl.controlledBatch (preComputes G j4 h4 j) (postComputes F G j)
    ((tables F G).outputBound F)

theorem query_length (j b : Bool) (r : UniversalPairReduction.Input s a) :
    ((targetEncoding (s:=s) (a:=a)).encode (queries G j4 h4 j r b)).length ≤
      (queriesComputes G j4 h4 j b).outputBound.bound.eval ((inputEncoding s a).encode r).length :=
  (queriesComputes G j4 h4 j b).outputBound.length_le r

theorem query_runtime (j b : Bool) (r : UniversalPairReduction.Input s a) :
    primitiveCost (queriesComputes G j4 h4 j b).machine
      ((queriesComputes G j4 h4 j b).outputs r).steps
      (some (Turing.initList (queriesComputes G j4 h4 j b).machine.computer ((inputEncoding s a).encode r))) ≤
    (primitivePolynomial (queriesComputes G j4 h4 j b)).eval ((inputEncoding s a).encode r).length :=
  computes_primitive_cost (queriesComputes G j4 h4 j b) r

namespace Replication
/-- ONE carrier vertex and ONE actual Eq4. Boundary order is
(Eq4.port1, carrier.port1, Eq4.port2, Eq4.port3). -/
abbrev arity : Bool → ℕ | false => 2 | true => 4
def port : (Σv : Bool,Fin (arity v)) → (Fin 4 ⊕ (Unit×Bool))
  | ⟨false,i⟩ => ![.inr ((),false),.inl 1] i
  | ⟨true,i⟩ => ![.inr ((),true),.inl 0,.inl 2,.inl 3] i
def portInv : (Fin 4 ⊕ (Unit×Bool)) → (Σv : Bool,Fin (arity v))
  | .inl i => ![⟨true,1⟩,⟨false,1⟩,⟨true,2⟩,⟨true,3⟩] i
  | .inr (_,false) => ⟨false,0⟩
  | .inr (_,true) => ⟨true,0⟩
def ports : (Σv : Bool,Fin (arity v)) ≃ (Fin 4 ⊕ (Unit×Bool)) where
  toFun := port
  invFun := portInv
  left_inv := by rintro ⟨v,i⟩; cases v <;> fin_cases i <;> rfl
  right_inv := by
    rintro (i|⟨u,b⟩)
    · fin_cases i <;> rfl
    · cases u; cases b <;> rfl
abbrev finite (j : Bool) : Holant.FiniteNetwork K Bool Unit 4 where
  arity := arity
  ports := ports
  vertex | false => fun x => pair G j (x 0) (x 1)
         | true => equalityFour
  edge _ := Signature.equality
abbrev graph (j : Bool) := (finite G j).toNetwork
def edgeBits : ((Unit×Bool)→Bool) ≃ (Bool×Bool) where
  toFun z := (z ((),false),z ((),true))
  invFun p := fun x => if x.2 then p.2 else p.1
  left_inv := by intro z; funext x; rcases x with ⟨u,b⟩; cases u; cases b <;> rfl
  right_inv := by rintro ⟨a,b⟩; rfl

theorem value (j : Bool) (x : Fin 4 → Bool) :
    (graph G j).denote x=pair G j (x 0) (x 1)*
      (if x 2=j then 1 else 0)*(if x 3=j then 1 else 0) := by
  rw [graph,Holant.FiniteNetwork.denote_toNetwork]
  unfold Holant.FiniteNetwork.denote
  simp only [finite]
  trans ∑ z : Bool × Bool,
    (∏ v : Bool,(finite G j).vertex v
      (fun i => Sum.elim x (edgeBits.symm z) (ports ⟨v,i⟩))) *
      ∏ e : Unit, Signature.equality ((edgeBits.symm z) (e,false)) ((edgeBits.symm z) (e,true))
  · let W := fun z : (Unit×Bool) → Bool =>
      (∏ v : Bool,(finite G j).vertex v (fun i => Sum.elim x z (ports ⟨v,i⟩))) *
        ∏ e : Unit, Signature.equality (z (e,false)) (z (e,true))
    have he := Fintype.sum_equiv edgeBits W (fun z => W (edgeBits.symm z))
      (fun z => by rw [Equiv.symm_apply_apply])
    convert he using 1 <;> congr 1 <;> (first | apply Subsingleton.elim | (ext z; simp))
  simp only [Fintype.sum_prod_type]
  cases j <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [finite,ports,port,edgeBits,Fintype.sum_bool,Fintype.prod_bool,
      pair,Signature.equality,equalityFour,Fin.forall_fin_succ,h0,h1,h2,h3]

/-- Closing with Eq, not X, gives the proved nonzero companion entry. -/
theorem closure (j : Bool) :
    (∑b : Bool,∑c : Bool,pair G j b c*Signature.equality b c)=companion G j j := by
  cases j <;> simp [pair,Signature.equality,Fintype.sum_bool]
theorem closure_nonzero (j : Bool) :
    (∑b : Bool,∑c : Bool,pair G j b c*Signature.equality b c)≠0 := by
  rw [closure]
  exact companion_nonzero G j

def labels (j : Bool) : Labelling (graph G j).shape (s+1) 1 (extendedArity s a) where
  vertex v := if (Fintype.equivFin Bool).symm v then Fin.castAdd 1 j4 else ⟨s,by omega⟩
  vertex_arity v := by
    change _ = arity ((Fintype.equivFin Bool).symm v)
    cases h : (Fintype.equivFin Bool).symm v
    · simp [extendedArity,graph,finite,arity,Holant.FiniteNetwork.toNetwork,h]
    · simpa [extendedArity,graph,finite,arity,Holant.FiniteNetwork.toNetwork,h,j4.isLt] using
        congrArg Sigma.fst h4
  edge _ := 0

theorem one_carrier (j : Bool) :
    (∑v : Fin (graph G j).shape.vertices,
      if ((labels G j4 h4 j).vertex v).val=s then (1 : ℕ) else 0)=1 := by
  trans ∑ v : Bool, if ((labels G j4 h4 j).vertex ((Fintype.equivFin Bool) v)).val=s then (1 : ℕ) else 0
  · apply Fintype.sum_equiv (Fintype.equivFin Bool).symm
    intro v
    simp only [Equiv.apply_symm_apply]
  · rw [Fintype.sum_bool]
    simp [labels,Nat.ne_of_lt j4.isLt]

theorem labelled_value (j : Bool) (x : Fin 4 → Bool) :
    ((labels G j4 h4 j).sourceNetwork (BinaryFamily.signatures G (pair G j))
      (fun _ : Fin 1 => Signature.equality)).denote x=
      pair G j (x 0) (x 1)*(if x 2=j then 1 else 0)*(if x 3=j then 1 else 0) := by
  rw [←value G j x]
  refine congrFun (Network.denote_congr _ _ _ _ _ ?_ ?_) x
  · have hv : ∀v : Fin (graph G j).shape.vertices,
        (⟨extendedArity s a ((labels G j4 h4 j).vertex v).val,
          BinaryFamily.signatures G (pair G j) ((labels G j4 h4 j).vertex v)⟩ : AnySignature K)=
            ⟨(graph G j).shape.arity v,(graph G j).vertex v⟩ := by
      intro v
      change (⟨extendedArity s a ((labels G j4 h4 j).vertex v).val,
        BinaryFamily.signatures G (pair G j) ((labels G j4 h4 j).vertex v)⟩ : AnySignature K)=
          ⟨arity ((Fintype.equivFin Bool).symm v),(finite G j).vertex ((Fintype.equivFin Bool).symm v)⟩
      dsimp only [labels]
      cases h : (Fintype.equivFin Bool).symm v
      · change (⟨extendedArity s a s,
          BinaryFamily.signatures G (pair G j) ⟨s,Nat.lt_succ_self s⟩⟩ : AnySignature K)=
            ⟨2,fun x => pair G j (x 0) (x 1)⟩
        apply Sigma.ext (by simp [extendedArity])
        have hd : 2=extendedArity s a s := by simp [extendedArity]
        have hs : BinaryFamily.signatures G (pair G j) ⟨s,Nat.lt_succ_self s⟩=
            (fun x : Fin (extendedArity s a s) → Bool =>
              pair G j (x (Fin.cast hd (0 : Fin 2))) (x (Fin.cast hd (1 : Fin 2)))) := by
          funext y
          simp only [BinaryFamily.signatures,Fin.val_mk,dite_eq_right (Nat.lt_irrefl s)] <;> rfl
        exact (heq_of_eq hs).trans (transportSignature_heq hd
          (fun x : Fin 2 → Bool => pair G j (x 0) (x 1)))
      · change (⟨extendedArity s a j4.val,
          BinaryFamily.signatures G (pair G j) (Fin.castAdd 1 j4)⟩ : AnySignature K)=
            ⟨4,equalityFour⟩
        apply Sigma.ext (by simpa [extendedArity,j4.isLt] using congrArg Sigma.fst h4)
        have hb : HEq (BinaryFamily.signatures G (pair G j) (Fin.castAdd 1 j4)) (G j4) := by
          have hd : a j4.val=extendedArity s a j4.val := by simp [extendedArity,j4.isLt]
          have hs : BinaryFamily.signatures G (pair G j) (Fin.castAdd 1 j4)=
              (fun x : Fin (extendedArity s a j4.val) → Bool =>
                G j4 (fun i => x (Fin.cast hd i))) := by
            funext y
            simp only [BinaryFamily.signatures,Fin.val_castAdd,dite_eq_left j4.isLt] <;> rfl
          exact (heq_of_eq hs).trans (transportSignature_heq hd (G j4))
        exact hb.trans (Sigma.mk.inj_iff.mp h4).2
    intro v y
    exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (BinaryFamily.signatures G (pair G j) ((labels G j4 h4 j).vertex v))
      ((graph G j).vertex v) (hv v) ((labels G j4 h4 j).vertex_arity v) y
  · intro e b c
    rfl
end Replication

end Ordinary

section Anchor
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (UniversalPairReduction.FiniteFamily.family G))
local instance : Algebra ℚ (QuaternaryAnchorAccess.K G A) := (QuaternaryAnchorAccess.K G A).algebra'
abbrev anchorField := QuaternaryAnchorAccess.presentation G A
def decoded (i : Fin (s+1)) : Signature (QuaternaryAnchorAccess.K G A)
    (QuaternaryAnchorAccess.arity G A i.val) :=
  fun x => (anchorField G A).decode ((QuaternaryAnchorAccess.tables G A).vertex i x)
def eq4Index : Fin (s+1) := ⟨s,Nat.lt_succ_self s⟩

private theorem mapAny_injective {K L : Type*} [Field K] [Field L] (φ : K →+* L) :
    Function.Injective (RingHomRealization.mapAny φ) := by
  rintro ⟨m,f⟩ ⟨n,g⟩ h
  have hn : m=n := congrArg Sigma.fst h
  subst n
  have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  congr 1
  funext x
  exact φ.injective (congrFun hf x)

theorem decoded_eq4 :
    (⟨QuaternaryAnchorAccess.arity G A s,decoded G A (eq4Index (s:=s))⟩ :
      AnySignature (QuaternaryAnchorAccess.K G A))=⟨4,equalityFour⟩ := by
  apply mapAny_injective (QuaternaryAnchorAccess.K G A).subtype
  change (⟨QuaternaryAnchorAccess.arity G A s,
    fun x => (((anchorField G A).decode ((QuaternaryAnchorAccess.tables G A).vertex
      (eq4Index (s:=s)) x) : QuaternaryAnchorAccess.K G A) : AlgebraicComplex)⟩ : AnySignature AlgebraicComplex)=
        ⟨4,RingHomRealization.mapSignature (QuaternaryAnchorAccess.K G A).subtype equalityFour⟩
  have hm : RingHomRealization.mapSignature (QuaternaryAnchorAccess.K G A).subtype equalityFour=
      (equalityFour : Signature AlgebraicComplex 4) := by
    funext x
    simp [RingHomRealization.mapSignature,equalityFour]
  rw [hm]
  exact QuaternaryAnchorAccess.eq4_label G A

theorem table_exact : tables (anchorField G A) (decoded G A)=QuaternaryAnchorAccess.tables G A := by
  unfold tables QuaternaryAnchorAccess.tables
  congr 1
  funext i x
  exact LinearEquiv.symm_apply_apply _ _

abbrev anchorInputEncoding := inputEncoding (s+1) (QuaternaryAnchorAccess.arity G A)
abbrev anchorCompanion (j : Bool) := companion (decoded G A) j
abbrev anchorValue (j : Bool) := value (decoded G A) (pair (decoded G A) j)

/-- The source uses the very same ordinary RG+Eq4 table and the same field.
No caller supplies Eq4 membership, companion nonzero, or a target reducer. -/
def anchorControlled (j : Bool) : LengthControlledOracleReduction
    (anchorInputEncoding G A) (anchorField G A).encoding
    (QuaternaryAnchorAccess.inputEncoding G A) (anchorField G A).encoding
    (anchorValue G A j) (QuaternaryAnchorAccess.value G A) := by
  have M := controlled (anchorField G A) (decoded G A) (eq4Index (s:=s)) (decoded_eq4 G A) j
  change LengthControlledOracleReduction _ _ _ _ _ ((tables (anchorField G A) (decoded G A)).evaluate _) at M
  rw [table_exact] at M
  exact M

abbrev Access (j : Bool) := PolyTimeOracleReduction
    (anchorInputEncoding G A) (anchorField G A).encoding
    (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
    (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
    (anchorValue G A j) (QuaternaryAnchorAccess.GOT.originalValue G)
def access (j : Bool) : Access G A j :=
  (anchorControlled G A j).compose (QuaternaryAnchorAccess.access G A)

def execution (j : Bool) (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
      (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
      (QuaternaryAnchorAccess.GOT.originalValue G) oracle)
    (r : UniversalPairReduction.Input (s+1) (QuaternaryAnchorAccess.arity G A)) :=
  (access G A j).correct oracle ho r

theorem anchorCompanion_nonzero (j : Bool) : anchorCompanion G A j j≠0 :=
  companion_nonzero (decoded G A) j

def anchorContext (j : Bool) :=
  Replication.labels (decoded G A) (eq4Index (s:=s)) (decoded_eq4 G A) j
theorem anchorContext_value (j : Bool) (x : Fin 4 → Bool) :
    ((anchorContext G A j).sourceNetwork
      (BinaryFamily.signatures (decoded G A) (pair (decoded G A) j))
      (fun _ : Fin 1 => Signature.equality)).denote x=
      pair (decoded G A) j (x 0) (x 1)*(if x 2=j then 1 else 0)*(if x 3=j then 1 else 0) :=
  Replication.labelled_value (decoded G A) (eq4Index (s:=s)) (decoded_eq4 G A) j x

section OriginalL
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
variable {L : Type} [Field L] [NumberField L]
variable (φ : L →ₐ[ℚ] AlgebraicComplex) (H : (i : Fin s) → Signature L (a i.val))
variable (B : QuaternaryEqualityTerminal.AnchorStep
  (UniversalPairReduction.FiniteFamily.family (OriginalLCodec.mapped φ H)))
def accessOriginalL (j : Bool) : PolyTimeOracleReduction
    (anchorInputEncoding (OriginalLCodec.mapped φ H) B)
    (anchorField (OriginalLCodec.mapped φ H) B).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (anchorValue (OriginalLCodec.mapped φ H) B j) (OriginalLCodec.value H) :=
  (anchorControlled (OriginalLCodec.mapped φ H) B j).compose
    (QuaternaryAnchorAccess.accessOriginalL φ H B)
end OriginalL
end Anchor
end Holant.LocalDrafts.MainChain.QuaternaryOrdinaryCompanion
