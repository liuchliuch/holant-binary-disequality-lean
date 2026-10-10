import Holant.Proofs.Algorithms.QuaternaryEqualityTerminal
import Holant.Proofs.BinaryInterpolation.SingularExtraction.RawGrouping
import Holant.Complexity.FixedGadgetSubstitution.Size
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Prefix
import Holant.Complexity.FixedFieldMachines.ScalarPower.Correction


namespace Holant.LocalDrafts.MainChain.QuaternaryReplicationMachine
open Holant.Complexity Holant.Algebraic
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant.Complexity.FixedFieldMachines
open RawClosedNetwork FixedGadgetSubstitution UniversalPairReduction
open UniversalPairReduction.Surgery
open QuaternaryEqualityTerminal
open scoped BigOperators

def squareArity (s : ℕ) (a : ℕ → ℕ) (i : ℕ) : ℕ := if i<s then a i else 4
abbrev Input (s : ℕ) (a : ℕ → ℕ) := ExactSignatureTables.Input (s+1) 1 (squareArity s a)
def count (s : ℕ) (rows : List RawVertex) : ℕ :=
  (rows.filter (fun row => row.1==s)).length
@[simp] theorem count_nil (s : ℕ) : count s []=0 := rfl
theorem count_cons (s : ℕ) (row : RawVertex) (rows : List RawVertex) :
    count s (row::rows)=(if row.1=s then 1 else 0)+count s rows := by
  by_cases h : row.1=s <;> simp [count,h,Nat.add_comm]

/-- next is the next fresh edge ID, not the count of processed rows.
The carrier is outside body and is never copied by the row recursion. -/
structure State where
  next : ℕ
  zeroPort : RawEndpoint
  onePort : RawEndpoint
  body : List RawVertex

def graft (j : ℕ) (st : State) (L : List RawEndpoint) : State where
  next := st.next+2
  zeroPort := (st.next,false)
  onePort := (st.next+1,false)
  body := (j,[(st.next,true),st.onePort,L.getD 1 (0,false),L.getD 3 (0,false)]) ::
    (j,[(st.next+1,true),st.zeroPort,L.getD 0 (0,false),L.getD 2 (0,false)]) :: st.body

/-- Fold right so old rows retain their relative order. Each square is
replaced by two q rows in its original position. The fresh edge interval
depends on the ACTUAL number of square occurrences in the suffix. -/
def expand (s j m : ℕ) : List RawVertex → State
  | [] => ⟨m+1,(m,false),(m,true),[]⟩
  | row::rows =>
      let st := expand s j m rows
      if row.1=s then graft j st row.2 else {st with body := row::st.body}

theorem expand_next (s j m : ℕ) (rows : List RawVertex) :
    (expand s j m rows).next=m+1+2*count s rows := by
  induction rows with
  | nil => simp [expand]
  | cons row rows ih =>
      rw [count_cons]
      by_cases h : row.1=s <;> simp [expand,h,graft,ih] <;> omega
theorem expand_length (s j m : ℕ) (rows : List RawVertex) :
    (expand s j m rows).body.length=rows.length+count s rows := by
  induction rows with
  | nil => simp [expand]
  | cons row rows ih =>
      rw [count_cons]
      by_cases h : row.1=s <;> simp [expand,h,graft,ih] <;> omega

def emitted (s : ℕ) (st : State) : List RawVertex :=
  (s,[st.zeroPort,st.onePort])::st.body
def raw (s j : ℕ) (r : RawClosedNetwork) : RawClosedNetwork :=
  let st := expand s j r.edges.length r.vertices
  ⟨emitted s st,r.edges++List.replicate (1+2*count s r.vertices) 0⟩

theorem raw_vertices (s j : ℕ) (r : RawClosedNetwork) :
    (raw s j r).vertices.length=r.vertices.length+count s r.vertices+1 := by
  simp [raw,emitted,expand_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem raw_edges (s j : ℕ) (r : RawClosedNetwork) :
    (raw s j r).edges.length=r.edges.length+1+2*count s r.vertices := by
  simp [raw,Nat.add_assoc]
theorem raw_edge_prefix (s j : ℕ) (r : RawClosedNetwork) :
    (raw s j r).edges.take r.edges.length=r.edges := by simp [raw]

def ends (st : State) : List RawEndpoint :=
  [st.zeroPort,st.onePort]++st.body.flatMap Prod.snd

theorem four_ports (L : List RawEndpoint) (h : L.length=4) :
    L=[L.getD 0 (0,false),L.getD 1 (0,false),L.getD 2 (0,false),L.getD 3 (0,false)] := by
  rcases L with _|⟨x0,L⟩ <;> simp only [List.length_nil,List.length_cons] at h
  · omega
  rcases L with _|⟨x1,L⟩ <;> simp only [List.length_nil,List.length_cons] at h
  · omega
  rcases L with _|⟨x2,L⟩ <;> simp only [List.length_nil,List.length_cons] at h
  · omega
  rcases L with _|⟨x3,L⟩ <;> simp only [List.length_nil,List.length_cons] at h
  · omega
  have he : L=[] := List.eq_nil_of_length_eq_zero (by omega)
  subst L
  rfl

/-- Exact multiset of port OCCURRENCES. A self-loop's two different sides
remain different entries; repeated edges and scalar components are allowed. -/
theorem graft_ends (j : ℕ) (st : State) (L : List RawEndpoint) (hL : L.length=4) :
    (ends (graft j st L)).Perm (L++ends st++edgeEnds st.next 2) := by
  have h := four_ports L hL
  conv_rhs => rw [h]
  apply List.perm_iff_count.mpr
  intro p
  simp [ends,graft,edgeEnds,List.range_succ,List.count_append,List.count_cons] <;> omega

theorem retained_ends (st : State) (row : RawVertex) :
    (ends {st with body := row::st.body}).Perm (row.2++ends st) := by
  apply List.perm_iff_count.mpr
  intro p
  simp [ends,List.count_append,List.count_cons] <;> omega

theorem expand_partition (s j m : ℕ) (rows : List RawVertex)
    (hw : ∀row∈rows,row.1=s → row.2.length=4) :
    (ends (expand s j m rows)).Perm
      (rows.flatMap Prod.snd++edgeEnds m (1+2*count s rows)) := by
  induction rows with
  | nil => simp [expand,ends,edgeEnds]
  | cons row rows ih =>
      have ih' := ih (fun u hu => hw u (by simp [hu]))
      by_cases h : row.1=s
      · have hp := graft_ends j (expand s j m rows) row.2 (hw row (by simp) h)
        have ht := (List.Perm.refl row.2).append (ih'.append
          (List.Perm.refl (edgeEnds (expand s j m rows).next 2)))
        have he : 1+2*count s (row::rows)=(1+2*count s rows)+2 := by
          rw [count_cons,if_pos h]; omega
        have hp' : (ends (graft j (expand s j m rows) row.2)).Perm
            (row.2 ++ (ends (expand s j m rows) ++ edgeEnds (expand s j m rows).next 2)) := by
          simpa only [List.append_assoc] using hp
        simpa only [expand,if_pos h,List.flatMap_cons,he,edgeEnds_add,expand_next,
          List.append_assoc,Nat.add_assoc] using hp'.trans ht
      · have hp := retained_ends (expand s j m rows) row
        have ht := (List.Perm.refl row.2).append ih'
        simpa [expand,h,count_cons,List.append_assoc] using hp.trans ht

theorem expand_labels {s : ℕ} {a : ℕ → ℕ} (j : Fin s) (hj : a j.val=4)
    (m : ℕ) (rows : List RawVertex)
    (hw : ∀row∈rows,row.1<s+1 ∧ row.2.length=squareArity s a row.1) :
    ∀row∈(expand s j.val m rows).body,row.1<s ∧ row.2.length=a row.1 := by
  induction rows with
  | nil => simp [expand]
  | cons row rows ih =>
      have ih' := ih (fun u hu => hw u (by simp [hu]))
      have hr := hw row (by simp)
      by_cases h : row.1=s
      · intro u hu
        simp only [expand,if_pos h,graft,List.mem_cons] at hu
        rcases hu with rfl|rfl|hu
        · exact ⟨j.isLt,by simpa using hj.symm⟩
        · exact ⟨j.isLt,by simpa using hj.symm⟩
        · exact ih' _ hu
      · have hlt : row.1<s := by omega
        intro u hu
        simp only [expand,if_neg h,List.mem_cons] at hu
        rcases hu with rfl|hu
        · exact ⟨hlt,by simpa [squareArity,hlt] using hr.2⟩
        · exact ih' _ hu

theorem valid {s : ℕ} {a : ℕ → ℕ} (j : Fin s) (hj : a j.val=4) (r : Input s a) :
    (raw s j.val r.val).WellFormed (s+1) 1 (extendedArity s a) := by
  have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  have hl := expand_labels j hj r.val.edges.length r.val.vertices hr.1
  apply (RawGrouping.wellFormed_iff_members _ _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro row hm
    simp only [raw,emitted,List.mem_cons] at hm
    rcases hm with rfl|hm
    · simp [extendedArity]
    · have hh := hl row hm
      exact ⟨by omega,by simpa [extendedArity,hh.1] using hh.2⟩
  · intro e he
    simp only [raw,List.mem_append,List.mem_replicate] at he
    rcases he with he|⟨_,rfl⟩
    · exact hr.2.1 _ he
    · decide
  · have hp := expand_partition s j.val r.val.edges.length r.val.vertices (by
      intro row hm he
      simpa [squareArity,he] using (hr.1 row hm).2)
    have ho : (r.val.vertices.flatMap Prod.snd).Perm (edgeEnds 0 r.val.edges.length) := by
      simpa [RawClosedNetwork.endpoints,expectedEndpoints_eq,List.flatMap] using hr.2.2
    have ht := ho.append (List.Perm.refl (edgeEnds r.val.edges.length (1+2*count s r.val.vertices)))
    have hf := hp.trans ht
    simpa [raw,emitted,ends,RawClosedNetwork.endpoints,expectedEndpoints_eq,
      edgeEnds_add,List.flatMap,Nat.add_assoc] using hf

theorem one_marked {s : ℕ} {a : ℕ → ℕ} (j : Fin s) (hj : a j.val=4) (r : Input s a) :
    FixedGadgetSubstitution.occurrences s (raw s j.val r.val)=1 := by
  have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  have hl := expand_labels j hj r.val.edges.length r.val.vertices hr.1
  have hn : ((expand s j.val r.val.edges.length r.val.vertices).body.filter
      (fun row => row.1==s))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro row hm
    simp [Nat.ne_of_lt (hl row hm).1]
  simp [FixedGadgetSubstitution.occurrences,raw,emitted,hn]

/-- A real raw producer, validated against the EXISTING one-pair input
language, with no desired query-validity or incidence premise. This alone
does not constitute a polynomial-time Boolean-stack Computes theorem. -/
def query {s : ℕ} {a : ℕ → ℕ} (j : Fin s) (hj : a j.val=4) (r : Input s a) :
    UniversalPairReduction.Input s a :=
  ⟨raw s j.val r.val,valid j hj r,by rw [one_marked j hj r]⟩

theorem count_le (s : ℕ) (rows : List RawVertex) : count s rows≤rows.length :=
  List.length_filter_le _ _

/-- Additional q resources are 2k; pre-existing occurrences of the same
original q index are retained and counted as well. -/
theorem original_q_count (s j m : ℕ) (hne : j≠s) (rows : List RawVertex) :
    count j (expand s j m rows).body=count j rows+2*count s rows := by
  induction rows with
  | nil => simp [expand]
  | cons row rows ih =>
      by_cases h : row.1=s
      · have hne' : row.1≠j := by rw [h]; exact hne.symm
        simp [expand,h,graft,count_cons,hne',hne,hne.symm,ih] <;> omega
      · simp [expand,h,count_cons,ih] <;> omega

theorem raw_q_count {s : ℕ} (j : Fin s) (r : RawClosedNetwork) :
    count j.val (raw s j.val r).vertices=count j.val r.vertices+2*count s r.vertices := by
  simpa [raw,emitted,count_cons,Nat.ne_of_lt j.isLt,(Nat.ne_of_lt j.isLt).symm] using
    original_q_count s j.val r.edges.length (Nat.ne_of_lt j.isLt) r.vertices

def arityBound (s : ℕ) (a : ℕ → ℕ) : ℕ :=
  max 4 (Finset.univ.sup (fun i : Fin s => a i.val))
theorem arity_le (s : ℕ) (a : ℕ → ℕ) (i : ℕ) (hi : i<s+1) :
    extendedArity s a i≤arityBound s a := by
  by_cases h : i<s
  · simp only [extendedArity,if_pos h]
    exact (Finset.le_sup (f:=fun j : Fin s => a j.val) (Finset.mem_univ (⟨i,h⟩ : Fin s))).trans (Nat.le_max_right 4 _)
  · simp only [extendedArity,if_neg h]
    exact (by decide : 2≤4).trans (Nat.le_max_left _ _)

noncomputable def querySize (s A : ℕ) : Polynomial ℕ :=
  2*((2*(2*Polynomial.C (s+1)+2+(4*(2*Polynomial.X+1)+6)*Polynomial.C A)+2)*
    (2*Polynomial.X+1)+1)+1+4*(2*Polynomial.X+1)+1

/-- Polynomial BIT length for the actual parser/encoder, not just a bound
on abstract vertices. This still does not supply a step-count proof for a
Boolean implementation of expand. -/
theorem query_length {s : ℕ} {a : ℕ → ℕ} (j : Fin s) (hj : a j.val=4) (r : Input s a) :
    ((UniversalPairReduction.inputEncoding s a).encode (query j hj r)).length≤
      (querySize s (arityBound s a)).eval (RawClosedNetwork.encoding.encode r.val).length := by
  have hb := raw_length_le (raw s j.val r.val) (valid j hj r) (arityBound s a) (arity_le s a)
  have hn := r.val.counts_le_encoded_length
  have hk := count_le s r.val.vertices
  have hv : (raw s j.val r.val).vertices.length≤2*(RawClosedNetwork.encoding.encode r.val).length+1 := by
    rw [raw_vertices]; omega
  have he : (raw s j.val r.val).edges.length≤2*(RawClosedNetwork.encoding.encode r.val).length+1 := by
    rw [raw_edges]; omega
  change (RawClosedNetwork.encoding.encode (raw s j.val r.val)).length≤_
  apply hb.trans
  simp only [querySize,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  simp only [Nat.add_assoc]
  gcongr <;> norm_num

/-- The exponent is read from the actual original label stream by the
existing compiler, not supplied as a size certificate or semantic oracle. -/
noncomputable def countComputes (s : ℕ) (a : ℕ → ℕ) :
    BinaryCompose.Computes (RawClosedNetwork.validatedEncoding (s+1) 1 (squareArity s a))
      GraphPreprocessing.UnaryBinary.unaryEncoding (fun r : Input s a => count s r.val.vertices) :=
  FixedGadgetSubstitution.Compiler.occurrencesComputes (s:=s+1) (b:=1)
    (arity:=squareArity s a) s

section Correction
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Holant.Signature Holant.Tractable.AlgebraicComplex (a i.val))
variable (j : Fin s)

/-- The scalar lies in the ORIGINAL whole-family coefficient field, since
it is the product of the two actual q entries. -/
noncomputable def scale : UniversalPairReduction.Source.field G :=
  fieldCoefficient (UniversalPairReduction.FiniteFamily.coefficient G) (.inl ⟨j,fun _ => false⟩) *
  fieldCoefficient (UniversalPairReduction.FiniteFamily.coefficient G) (.inl ⟨j,fun _ => true⟩)

theorem scale_exact : (scale G j : Holant.Tractable.AlgebraicComplex)=
    G j (fun _ => false)*G j (fun _ => true) := rfl

theorem scale_nonzero {q : Holant.Signature Holant.Tractable.AlgebraicComplex 4}
    (hj : (⟨a j.val,G j⟩ : Holant.AnySignature Holant.Tractable.AlgebraicComplex)=⟨4,q⟩)
    (P : QuaternaryEqualityTerminal.PureStep q) : scale G j≠0 := by
  have h0 := BinaryInterpolation.Chains.signature_cast_apply (G j) q hj
    (congrArg Sigma.fst hj) (fun _ => false)
  have h1 := BinaryInterpolation.Chains.signature_cast_apply (G j) q hj
    (congrArg Sigma.fst hj) (fun _ => true)
  have hq0 : q (fun _ => false)=P.left := (congrFun P.original _).trans
    (Holant.EightVertex.ProductAnchor.ge4_left _ _ _)
  have hq1 : q (fun _ => true)=P.right := (congrFun P.original _).trans
    (Holant.EightVertex.ProductAnchor.ge4_right _ _ _)
  intro hz
  have hz' := congrArg (fun z : UniversalPairReduction.Source.field G =>
    (z : Holant.Tractable.AlgebraicComplex)) hz
  change G j (fun _ => false)*G j (fun _ => true)=0 at hz'
  rw [h0,h1,hq0,hq1] at hz'
  exact P.scale_ne_zero hz'

/-- A real existing scalar-power machine on (answer,k) in the SAME codec
as onePair. No query compiler or global value equality is smuggled into it. -/
noncomputable def correction := FixedFieldMachines.ScalarPower.correction
  (UniversalPairReduction.Source.presentation G (QuaternaryEqualityTerminal.algebraic G)) (scale G j)
end Correction


theorem empty_raw (s j : ℕ) : raw s j ⟨[],[]⟩=
    ⟨[(s,[(0,false),(0,true)])],[0]⟩ := rfl
theorem no_square {s j : ℕ} (r : RawClosedNetwork) (h : count s r.vertices=0) :
    raw s j r=⟨(s,[(r.edges.length,false),(r.edges.length,true)])::r.vertices,r.edges++[0]⟩ := by
  have he : ∀rows,count s rows=0 → expand s j r.edges.length rows=
      ⟨r.edges.length+1,(r.edges.length,false),(r.edges.length,true),rows⟩ := by
    intro rows
    induction rows with
    | nil => intro _; rfl
    | cons row rows ih =>
        intro hc
        rw [count_cons] at hc
        have hn : row.1≠s := by intro hh; simp [hh] at hc
        have ht : count s rows=0 := by simp [hn] at hc; exact hc
        simp [expand,hn,ih ht]
  simp [raw,he _ h,h,emitted]

/-- The sole fresh local value identity, valid even if old endpoints are
on the same original edge. It is the already proved OPEN step, specialized
to the six actual endpoint bits; no new independence premise appears. -/
theorem graft_value (q : Holant.Signature Holant.Tractable.AlgebraicComplex 4)
    (P : QuaternaryEqualityTerminal.PureStep q) (z0 z1 u0 u1 u2 u3 : Bool) :
    (QuaternaryEqualityTerminal.step q).denote ![z0,z1,u0,u1,u2,u3]=
      (P.left*P.right)*
        QuaternaryEqualityTerminal.delta ![z0,z1]*
        QuaternaryEqualityTerminal.square ![u0,u1,u2,u3] := by
  rw [P.value]
  cases z0 <;> cases z1 <;> cases u0 <;> cases u1 <;> cases u2 <;> cases u3 <;>
    simp [Holant.Signature.tensor_apply,delta,square,BinaryTable.delta,mul_assoc]

/-- The two newly appended edges have independent Boolean choices u,v.
Their false endpoints meet the unique carrier and their true endpoints
meet the q vertices. Old bits may coincide (including original self-loops).
This is the local summation identity needed by a global fold proof. -/
theorem graft_contraction (q : Holant.Signature Holant.Tractable.AlgebraicComplex 4)
    (P : QuaternaryEqualityTerminal.PureStep q) (z0 z1 x0 x1 x2 x3 : Bool) :
    (∑u : Bool, ∑v : Bool,
      QuaternaryEqualityTerminal.delta ![!u,!v] * q ![u,z1,x1,x3] * q ![v,z0,x0,x2])=
      (P.left*P.right)*QuaternaryEqualityTerminal.delta ![z0,z1]*
        QuaternaryEqualityTerminal.square ![x0,x1,x2,x3] := by
  have h := graft_value q P z0 z1 x0 x1 x2 x3
  rw [QuaternaryEqualityTerminal.step_value] at h
  simpa [QuaternaryEqualityTerminal.delta,UniversalPairReduction.BinaryTable.delta] using h

/-! The next section sums the ACTUAL appended edges. It does not evaluate a
Holant instance in polynomial time: these sums are semantic proof objects. -/
noncomputable section Semantics
open UniversalPairReduction.Surgery.Choice
set_option backward.isDefEq.respectTransparency false

def put (c : ℕ → Bool) (e : ℕ) (b : Bool) : ℕ → Bool :=
  fun i => if i=e then b else c i

theorem bit_put_old (c : ℕ → Bool) (e : ℕ) (b : Bool) (p : RawEndpoint)
    (hp : p.1<e) : bit (put c e b) p=bit c p := by
  simp [bit,put,Nat.ne_of_lt hp]

theorem row_put_old {K : Type*} (F : Table K) (c : ℕ → Bool)
    (e : ℕ) (b : Bool) (row : RawVertex) (h : ∀p∈row.2,p.1<e) :
    rowValue F (put c e b) row=rowValue F c row := by
  unfold rowValue
  congr 1
  exact List.map_congr_left (fun p hp => bit_put_old c e b p (h p hp))

theorem weight_put_old {K : Type*} [CommSemiring K] (F : Table K)
    (c : ℕ → Bool) (e : ℕ) (b : Bool) (rows : List RawVertex)
    (h : ∀row∈rows,∀p∈row.2,p.1<e) :
    Choice.weight F (put c e b) rows=Choice.weight F c rows := by
  unfold Choice.weight
  congr 1
  exact List.map_congr_left (fun row hr => row_put_old F c e b row (h row hr))

/-- Split off the actual LAST edge, leaving all old indices unchanged. -/
def lastChoice (n : ℕ) : (Fin (n+1) → Bool) ≃ ((Fin n → Bool) × Bool) where
  toFun c := (fun i => c i.castSucc,c (Fin.last n))
  invFun d i := if h : i.val<n then d.1 ⟨i.val,h⟩ else d.2
  left_inv := by
    intro c; funext i
    by_cases h : i.val<n
    · simp [h]
    · have hi : i=Fin.last n := Fin.ext (by simp; omega)
      subst i
      simp
  right_inv := by
    rintro ⟨c,b⟩
    apply Prod.ext
    · funext i; simp [i.isLt]
    · simp

theorem extend_last (n : ℕ) (d : (Fin n → Bool) × Bool) :
    extend ((lastChoice n).symm d)=put (extend d.1) n d.2 := by
  funext i
  by_cases hi : i<n
  · simp [extend,lastChoice,put,hi,show i<n+1 by omega,Nat.ne_of_lt hi]
  · by_cases he : i=n
    · subst i; simp [extend,lastChoice,put]
    · simp [extend,lastChoice,put,hi,he,show ¬i<n+1 by omega]

theorem sum_last {K : Type*} [AddCommMonoid K] (n : ℕ) (f : (ℕ → Bool) → K) :
    (∑c : Fin (n+1) → Bool,f (extend c))=
      ∑c : Fin n → Bool,∑b : Bool,f (put (extend c) n b) := by
  rw [←(lastChoice n).symm.sum_comp]
  simp only [extend_last,Fintype.sum_prod_type]

/-- Sum only over the fresh interval [m,m+n), fixing every original edge.
The recursion order matches the two last edges allocated by graft. -/
def fresh {K : Type*} [AddCommMonoid K] (m : ℕ) :
    ℕ → ((ℕ → Bool) → K) → (ℕ → Bool) → K
  | 0,f,c => f c
  | n+1,f,c => fresh m n (fun d => ∑b : Bool,f (put d (m+n) b)) c

theorem sum_fresh {K : Type*} [AddCommMonoid K] (m n : ℕ)
    (f : (ℕ → Bool) → K) :
    (∑c : Fin (m+n) → Bool,f (extend c))=
      ∑c : Fin m → Bool,fresh m n f (extend c) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      rw [show m+(n+1)=(m+n)+1 by omega,sum_last]
      exact ih (fun d => ∑ b : Bool, f (put d (m+n) b))

theorem fresh_congr {K : Type*} [AddCommMonoid K] (m n : ℕ)
    {f g : (ℕ → Bool) → K} (h : ∀c,f c=g c) (c : ℕ → Bool) :
    fresh m n f c=fresh m n g c := by
  have he : f=g := funext h
  rw [he]

theorem fresh_const_mul {K : Type*} [Semiring K] (m n : ℕ) (A : K)
    (f : (ℕ → Bool) → K) (c : ℕ → Bool) :
    fresh m n (fun d => A*f d) c=A*fresh m n f c := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simpa only [fresh,←Finset.mul_sum] using
        (ih (fun d => ∑b : Bool,f (put d (m+n) b)))

theorem fresh_pull {K : Type*} [Semiring K] (m n : ℕ)
    (g f : (ℕ → Bool) → K)
    (hg : ∀c e b,m≤e → g (put c e b)=g c) (c : ℕ → Bool) :
    fresh m n (fun d => g d*f d) c=g c*fresh m n f c := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [fresh]
      have he : (fun d => ∑b : Bool,g (put d (m+n) b)*f (put d (m+n) b))=
          (fun d => g d*∑b : Bool,f (put d (m+n) b)) := by
        funext d
        simp only [hg d (m+n) _ (by omega),Finset.mul_sum]
      rw [he]
      exact ih _

theorem expand_bound (s j m : ℕ) (rows : List RawVertex)
    (hw : ∀row∈rows,row.1=s → row.2.length=4)
    (hb : ∀row∈rows,∀p∈row.2,p.1<m) :
    ∀p∈ends (expand s j m rows),p.1<(expand s j m rows).next := by
  intro p hp
  have hh := (expand_partition s j m rows hw).mem_iff.mp hp
  rcases List.mem_append.mp hh with hh|hh
  · rcases List.mem_flatMap.mp hh with ⟨row,hr,hp⟩
    have h := hb row hr p hp
    rw [expand_next]; omega
  · have h := (Template.mem_edgeEnds m (1+2*count s rows) p).mp hh
    rw [expand_next]; omega

section SourceTable
variable {K : Type*} [CommSemiring K]
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Holant.Signature K (a i.val))

/-- Literal source table: original labels are unchanged; only label s has
the four ordered entries Delta tensor Delta. No free-pin interpretation. -/
def squareSignatures (i : Fin (s+1)) : Holant.Signature K (squareArity s a i.val) :=
  fun x => if hi : i.val<s then
    G ⟨i.val,hi⟩ (fun j => x (Fin.cast (by simp [squareArity,hi]) j))
  else QuaternaryEqualityTerminal.square
    (fun j => x (Fin.cast (by simp [squareArity,hi]) j))

abbrev squareTable := Choice.table (squareSignatures G)
abbrev deltaTable := Choice.table (BinaryFamily.signatures G BinaryTable.delta)

theorem square_table_old (i : ℕ) (hi : i<s) (bits : List Bool) :
    squareTable G i bits=Choice.table G i bits := by
  simp [squareTable,Choice.table,squareSignatures,hi,show i<s+1 by omega]

theorem square_table_new (bits : List Bool) : squareTable G s bits=
    QuaternaryEqualityTerminal.square (fun i => bits.getD i.val false) := by
  simp [squareTable,Choice.table,squareSignatures]

def squareValue (r : Input s a) : K :=
  (r.val.realize r.property (squareSignatures G)
    (fun _ : Fin 1 => Holant.Signature.disequality)).denote Fin.elim0

theorem square_value_evaluate (r : Input s a) : squareValue G r=
    Choice.evaluate (squareTable G) r.val.edges.length r.val.vertices :=
  Choice.denote_eq_evaluate r.val r.property (squareSignatures G)

end SourceTable

section Family
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Holant.Signature Holant.Tractable.AlgebraicComplex (a i.val))

variable (j : Fin s) {q : Holant.Signature Holant.Tractable.AlgebraicComplex 4}
variable (hj : (⟨a j.val,G j⟩ : Holant.AnySignature Holant.Tractable.AlgebraicComplex)=⟨4,q⟩)
variable (P : QuaternaryEqualityTerminal.PureStep q)

include hj in
theorem q_table (x0 x1 x2 x3 : Bool) :
    deltaTable G j.val [x0,x1,x2,x3]=q ![x0,x1,x2,x3] := by
  unfold deltaTable
  rw [BinaryFamily.table_old G BinaryTable.delta j.val j.isLt]
  simp only [Choice.table,dif_pos j.isLt]
  have h := BinaryInterpolation.Chains.signature_cast_apply (G j) q hj
    (congrArg Sigma.fst hj) ![x0,x1,x2,x3]
  rw [←h]
  congr 1
  funext i
  have hi : i.val<4 := by
    have har : a j.val=4 := congrArg Sigma.fst hj
    omega
  change [x0,x1,x2,x3].getD i.val false=(![x0,x1,x2,x3] : Fin 4 → Bool) ⟨i.val,hi⟩
  have hv (t : Fin 4) : [x0,x1,x2,x3].getD t.val false=(![x0,x1,x2,x3] : Fin 4 → Bool) t := by
    fin_cases t <;> rfl
  exact hv ⟨i.val,hi⟩

include hj in
/-- Contraction for the literal emitted rows, with unchanged old body.
All bounds below concern incidence, and are internally produced by expand. -/
theorem graft_sum (st : State) (L : List RawEndpoint) (hL : L.length=4)
    (hs : ∀p∈ends st,p.1<st.next) (hB : ∀p∈L,p.1<st.next) (c : ℕ → Bool) :
    (∑u : Bool,∑v : Bool,Choice.weight (deltaTable G)
      (put (put c st.next u) (st.next+1) v) (emitted s (graft j.val st L)))=
      (P.left*P.right)*rowValue (squareTable G) c (s,L)*
        Choice.weight (deltaTable G) c (emitted s st) := by
  have hz := hs st.zeroPort (by simp [ends])
  have ho := hs st.onePort (by simp [ends])
  have hbody : ∀row∈st.body,∀p∈row.2,p.1<st.next := by
    intro row hr p hp
    exact hs p (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row,hr,hp⟩)))
  have hweight (u v : Bool) :
      Choice.weight (deltaTable G) (put (put c st.next u) (st.next+1) v) st.body=
        Choice.weight (deltaTable G) c st.body := by
    rw [weight_put_old _ _ _ _ _ (by intro row hr p hp; have := hbody row hr p hp; omega),
      weight_put_old _ _ _ _ _ hbody]
  have hports := four_ports L hL
  obtain ⟨p0,p1,p2,p3,hports'⟩ : ∃p0 p1 p2 p3,L=[p0,p1,p2,p3] :=
    ⟨_,_,_,_,hports⟩
  subst L
  have hb0 := hB p0 (by simp)
  have hb1 := hB p1 (by simp)
  have hb2 := hB p2 (by simp)
  have hb3 := hB p3 (by simp)
  have term (u v : Bool) :
      Choice.weight (deltaTable G) (put (put c st.next u) (st.next+1) v)
        (emitted s (graft j.val st [p0,p1,p2,p3]))=
      (QuaternaryEqualityTerminal.delta ![!u,!v]*
        q ![u,bit c st.onePort,bit c p1,bit c p3]*
        q ![v,bit c st.zeroPort,bit c p0,bit c p2]) *
        Choice.weight (deltaTable G) c st.body := by
    simp only [emitted,graft,weight_cons,rowValue,List.map_cons,List.map_nil,
      List.getD_cons_zero,List.getD_cons_succ]
    rw [hweight]
    simp only [deltaTable,BinaryFamily.table_pair]
    simp only [bit,put,show st.next≠st.next+1 by omega,if_false,if_true,
      Nat.ne_of_lt hz,Nat.ne_of_lt ho,Nat.ne_of_lt hb0,Nat.ne_of_lt hb1,
      Nat.ne_of_lt hb2,Nat.ne_of_lt hb3,
      show st.zeroPort.1≠st.next+1 by omega,show st.onePort.1≠st.next+1 by omega,
      show p0.1≠st.next+1 by omega,show p1.1≠st.next+1 by omega,
      show p2.1≠st.next+1 by omega,show p3.1≠st.next+1 by omega]
    have hq := q_table G j hj
    dsimp only [deltaTable] at hq
    rw [hq,hq]
    simp only [QuaternaryEqualityTerminal.delta,Matrix.cons_val_zero,Matrix.cons_val_one,
      Bool.false_eq_true,ite_false]
    ring
  simp_rw [term]
  simp_rw [←Finset.sum_mul]
  rw [graft_contraction q P]
  simp [rowValue,square_table_new,emitted,weight_cons,deltaTable,
    BinaryFamily.table_pair,QuaternaryEqualityTerminal.delta,
    QuaternaryEqualityTerminal.square,Holant.Signature.tensor_apply,mul_assoc,mul_comm,mul_left_comm]

include hj in
/-- All fresh edges contracted while every original edge is still fixed.
This stronger statement retains correlations between arbitrary old ports. -/
theorem expand_fresh (m : ℕ) (rows : List RawVertex)
    (hw : ∀row∈rows,row.1<s+1 ∧ row.2.length=squareArity s a row.1)
    (hb : ∀row∈rows,∀p∈row.2,p.1<m) (c : ℕ → Bool) :
    fresh m (1+2*count s rows)
      (fun d => Choice.weight (deltaTable G) d (emitted s (expand s j.val m rows))) c=
      (P.left*P.right)^count s rows * Choice.weight (squareTable G) c rows := by
  revert hw hb
  induction rows with
  | nil =>
      intro hw hb
      simp [count,expand,emitted,fresh,Choice.weight, rowValue,deltaTable,
        BinaryFamily.table_pair,bit,put,BinaryTable.delta,Fintype.sum_bool]
  | cons row rows ih =>
      intro hw hb
      have hwt := fun u hu => hw u (List.mem_cons_of_mem _ hu)
      have hbt := fun u hu => hb u (List.mem_cons_of_mem _ hu)
      have hrow := hw row (by simp)
      have hrowb := hb row (by simp)
      have hpull (e : ℕ) (b : Bool) (d : ℕ → Bool) (he : m≤e) :
          rowValue (squareTable G) (put d e b) row=rowValue (squareTable G) d row :=
        row_put_old _ _ _ _ _ (fun p hp => (hrowb p hp).trans_le he)
      by_cases hh : row.1=s
      · have hlen : row.2.length=4 := by simpa [squareArity,hh] using hrow.2
        have hroweq : (s,row.2)=row := Prod.ext hh.symm rfl
        have hn : 1+2*count s (row::rows)=(1+2*count s rows)+2 := by
          rw [count_cons,if_pos hh]; omega
        have hs := expand_bound s j.val m rows
          (fun u hu he => by simpa [squareArity,he] using (hwt u hu).2) hbt
        have hnext := expand_next s j.val m rows
        have hc (d : ℕ → Bool) := graft_sum G j hj P (expand s j.val m rows)
          row.2 hlen hs (fun p hp => by have := hrowb p hp; rw [hnext]; omega) d
        rw [hn]
        simp only [expand,if_pos hh,fresh]
        change fresh m (1+2*count s rows) _ c=_
        have heq := fresh_congr m (1+2*count s rows)
          (fun d => by simpa only [hnext,hroweq,Nat.add_assoc] using hc d) c
        simp only [Nat.add_assoc]
        rw [heq]
        have hf : (fun d => (P.left*P.right)*rowValue (squareTable G) d row *
            Choice.weight (deltaTable G) d (emitted s (expand s j.val m rows))) =
            (fun d => (P.left*P.right)*(rowValue (squareTable G) d row *
              Choice.weight (deltaTable G) d (emitted s (expand s j.val m rows)))) := by
          funext d; exact mul_assoc _ _ _
        rw [hf,fresh_const_mul,fresh_pull m _ _ _ (fun d e b he => hpull e b d he),ih hwt hbt]
        simp [count_cons,hh,weight_cons,pow_add,mul_assoc,mul_comm,mul_left_comm]
      · have hlt : row.1<s := by omega
        have hsame (d : ℕ → Bool) : rowValue (deltaTable G) d row=
            rowValue (squareTable G) d row := by
          simp [rowValue,deltaTable,BinaryFamily.table_old,square_table_old,hlt]
        have heq (d : ℕ → Bool) :
            Choice.weight (deltaTable G) d (emitted s (expand s j.val m (row::rows)))=
              rowValue (squareTable G) d row *
                Choice.weight (deltaTable G) d (emitted s (expand s j.val m rows)) := by
          simp only [expand,if_neg hh,emitted,weight_cons]
          rw [hsame]
          ring
        have hn : count s (row::rows)=count s rows := by simp [count_cons,hh]
        rw [hn,fresh_congr _ _ heq,
          fresh_pull m _ _ _ (fun d e b he => hpull e b d he),ih hwt hbt]
        rw [weight_cons]
        ring

/-- Global identity for the exact serialized graph emitted by query. The
only signature premise is the actual pure-ge event and its original label. -/
theorem query_value (r : Input s a) :
    BinaryFamily.value G BinaryTable.delta (query j (congrArg Sigma.fst hj) r)=
      (P.left*P.right)^count s r.val.vertices * squareValue G r := by
  have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  have hb : ∀row∈r.val.vertices,∀p∈row.2,p.1<r.val.edges.length := by
    intro row hrow p hp
    have hm : p∈r.val.vertices.flatMap Prod.snd := List.mem_flatMap.mpr ⟨row,hrow,hp⟩
    have he : (r.val.vertices.flatMap Prod.snd).Perm (edgeEnds 0 r.val.edges.length) := by
      simpa [RawClosedNetwork.endpoints,expectedEndpoints_eq,List.flatMap] using hr.2.2
    exact (ends_mem _ _).mp (he.mem_iff.mp hm)
  rw [BinaryFamily.value_evaluate,square_value_evaluate]
  change Choice.evaluate (deltaTable G) (raw s j.val r.val).edges.length
    (emitted s (expand s j.val r.val.edges.length r.val.vertices))=_
  rw [raw_edges,show r.val.edges.length+1+2*count s r.val.vertices=
    r.val.edges.length+(1+2*count s r.val.vertices) by omega]
  unfold Choice.evaluate
  rw [sum_fresh r.val.edges.length (1+2*count s r.val.vertices)
    (fun c => Choice.weight (deltaTable G) c (emitted s (expand s j.val r.val.edges.length r.val.vertices)))]
  simp_rw [expand_fresh G j hj P _ _ hr.1 hb]
  rw [Finset.mul_sum]

include hj in
theorem scale_pure : (scale G j : Holant.Tractable.AlgebraicComplex)=P.left*P.right := by
  have h0 := BinaryInterpolation.Chains.signature_cast_apply (G j) q hj
    (congrArg Sigma.fst hj) (fun _ => false)
  have h1 := BinaryInterpolation.Chains.signature_cast_apply (G j) q hj
    (congrArg Sigma.fst hj) (fun _ => true)
  have hq0 : q (fun _ => false)=P.left := (congrFun P.original _).trans
    (Holant.EightVertex.ProductAnchor.ge4_left _ _ _)
  have hq1 : q (fun _ => true)=P.right := (congrFun P.original _).trans
    (Holant.EightVertex.ProductAnchor.ge4_right _ _ _)
  rw [scale_exact,h0,h1,hq0,hq1]

/-- The square-source answer uses the old one-pair ORIGINAL family field
and its exact presentation, not a newly chosen extension or an AC codec. -/
abbrev squareFieldValue (r : Input s a) : UniversalPairReduction.Source.field G :=
  squareValue (ValueJoins.signatures
    (UniversalPairReduction.Source.presentation G (QuaternaryEqualityTerminal.algebraic G))
    (UniversalPairReduction.Source.tables G (QuaternaryEqualityTerminal.algebraic G))) r

theorem square_field_exact (r : Input s a) :
    (squareFieldValue G r : Holant.Tractable.AlgebraicComplex)=squareValue G r := by
  unfold squareFieldValue squareValue
  change (UniversalPairReduction.Source.field G).subtype _ = _
  rw [←Holant.Network.denote_map (UniversalPairReduction.Source.field G).subtype]
  congr 1
  unfold Holant.Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    dsimp only
    unfold squareSignatures
    split_ifs with hi
    · exact familyCoordinates_spec (UniversalPairReduction.FiniteFamily.coefficient G)
        (UniversalPairReduction.FiniteFamily.coefficient_algebraic G
          (QuaternaryEqualityTerminal.algebraic G)) _
    · simp only [QuaternaryEqualityTerminal.square,Holant.Signature.tensor_apply,
        QuaternaryEqualityTerminal.delta,BinaryTable.delta,map_mul]
      split_ifs <;> simp
  · funext e a b
    cases a <;> cases b <;> rfl

include P in
/-- The exact field-valued equation needed by the controlled caller. The
coefficient-field embedding is injective; no arbitrary reduction composition. -/
theorem query_value_field (r : Input s a) :
    UniversalPairReduction.Source.sourceValue G (QuaternaryEqualityTerminal.algebraic G)
      (query j (congrArg Sigma.fst hj) r)=
      (scale G j)^count s r.val.vertices * squareFieldValue G r := by
  apply Subtype.val_injective
  rw [UniversalPairReduction.Source.source_value_exact]
  change BinaryFamily.value G BinaryTable.delta (query j (congrArg Sigma.fst hj) r)=
    (scale G j : Holant.Tractable.AlgebraicComplex)^count s r.val.vertices *
      (squareFieldValue G r : Holant.Tractable.AlgebraicComplex)
  rw [scale_pure G j hj P,square_field_exact,query_value G j hj P]

/-- Correct execution of the ALREADY existing scalar correction, on the
actual single-Delta answer and the count read from the original source.
This is not yet an execution theorem for producing that query. -/
noncomputable def correction_answer (P : QuaternaryEqualityTerminal.PureStep q) (r : Input s a) :
    Turing.TM2OutputsInTime (correction G j).machine.computer
      ((pairEncoding
        (UniversalPairReduction.Source.presentation G (QuaternaryEqualityTerminal.algebraic G)).encoding
        GraphPreprocessing.UnaryBinary.unaryEncoding).encode
        (UniversalPairReduction.Source.sourceValue G (QuaternaryEqualityTerminal.algebraic G)
          (query j (congrArg Sigma.fst hj) r),count s r.val.vertices))
      (some ((UniversalPairReduction.Source.presentation G
        (QuaternaryEqualityTerminal.algebraic G)).encoding.encode (squareFieldValue G r)))
      ((correction G j).time.eval
        ((pairEncoding
          (UniversalPairReduction.Source.presentation G (QuaternaryEqualityTerminal.algebraic G)).encoding
          GraphPreprocessing.UnaryBinary.unaryEncoding).encode
          (UniversalPairReduction.Source.sourceValue G (QuaternaryEqualityTerminal.algebraic G)
            (query j (congrArg Sigma.fst hj) r),count s r.val.vertices)).length) := by
  rw [query_value_field G j hj P]
  exact FixedFieldMachines.ScalarPower.correct_answer
    (UniversalPairReduction.Source.presentation G (QuaternaryEqualityTerminal.algebraic G))
    (scale G j) (squareFieldValue G r) (scale_nonzero G j hj P) (count s r.val.vertices)

end Family
end Semantics
end Holant.LocalDrafts.MainChain.QuaternaryReplicationMachine
