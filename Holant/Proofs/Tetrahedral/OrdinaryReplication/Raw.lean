import Holant.Proofs.Algorithms.QuaternaryOrdinaryCompanion
import Holant.Proofs.Algorithms.QuaternaryReplicationMachine


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication
open Holant Holant.Complexity Holant.Algebraic
open FixedGadgetSubstitution RawClosedNetwork UniversalPairReduction
open UniversalPairReduction.Surgery
open scoped BigOperators
open Holant.LocalDrafts.MainChain

set_option backward.isDefEq.respectTransparency false

abbrev Input (s : ℕ) (a : ℕ → ℕ) := ExactSignatureTables.Input (s+1) 1 (extendedArity s a)
abbrev count := QuaternaryReplicationMachine.count

/-- The literal machine count, stated on this module's alias so recursion
proofs retain the SAME atom on both sides of their arithmetic identities. -/
@[simp] theorem count_nil (s : ℕ) : count s []=0 := rfl
theorem count_cons (s : ℕ) (row : RawVertex) (rows : List RawVertex) :
    count s (row::rows)=(if row.1=s then 1 else 0)+count s rows :=
  QuaternaryReplicationMachine.count_cons s row rows

structure State where
  next : ℕ
  carrierPort : RawEndpoint
  otherPort : RawEndpoint
  body : List RawVertex

/-- The carrier's first port moves to the new edge. Its second port is
retained. Eq4 ports are (new edge, old carrier, old ordered pair). -/
def graft (j4 : ℕ) (st : State) (L : List RawEndpoint) : State where
  next := st.next+1
  carrierPort := (st.next,false)
  otherPort := st.otherPort
  body := (j4,[(st.next,true),st.carrierPort,L.getD 0 (0,false),L.getD 1 (0,false)])::st.body

def expand (s j4 m : ℕ) : List RawVertex → State
  | [] => ⟨m+1,(m,false),(m,true),[]⟩
  | row::rows =>
      let st := expand s j4 m rows
      if row.1=s then graft j4 st row.2 else {st with body := row::st.body}

theorem expand_next (s j4 m : ℕ) (rows : List RawVertex) :
    (expand s j4 m rows).next=m+1+count s rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rw [count_cons]
      by_cases h : row.1=s <;> simp [expand,h,graft,ih] <;> omega

theorem expand_length (s j4 m : ℕ) (rows : List RawVertex) :
    (expand s j4 m rows).body.length=rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => by_cases h : row.1=s <;> simp [expand,h,graft,ih]

def emitted (s : ℕ) (st : State) : List RawVertex :=
  (s,[st.carrierPort,st.otherPort])::st.body
def raw (s j4 : ℕ) (r : RawClosedNetwork) : RawClosedNetwork :=
  ⟨emitted s (expand s j4 r.edges.length r.vertices),
    r.edges++List.replicate (1+count s r.vertices) 0⟩

theorem raw_vertices (s j4 : ℕ) (r : RawClosedNetwork) :
    (raw s j4 r).vertices.length=r.vertices.length+1 := by simp [raw,emitted,expand_length]
theorem raw_edges (s j4 : ℕ) (r : RawClosedNetwork) :
    (raw s j4 r).edges.length=r.edges.length+1+count s r.vertices := by simp [raw,Nat.add_assoc]
theorem raw_edge_prefix (s j4 : ℕ) (r : RawClosedNetwork) :
    (raw s j4 r).edges.take r.edges.length=r.edges := by simp [raw]

def ends (st : State) := [st.carrierPort,st.otherPort]++st.body.flatMap Prod.snd
theorem two_ports (L : List RawEndpoint) (hL : L.length=2) :
    L=[L.getD 0 (0,false),L.getD 1 (0,false)] := by
  rcases L with _|⟨p,L⟩ <;> simp only [List.length_nil,List.length_cons] at hL
  · omega
  rcases L with _|⟨q,L⟩ <;> simp only [List.length_nil,List.length_cons] at hL
  · omega
  have hn : L=[] := List.eq_nil_of_length_eq_zero (by omega)
  subst L
  rfl

theorem graft_ends (j4 : ℕ) (st : State) (L : List RawEndpoint) (hL : L.length=2) :
    (ends (graft j4 st L)).Perm (L++ends st++edgeEnds st.next 1) := by
  conv_rhs => rw [two_ports L hL]
  apply List.perm_iff_count.mpr
  intro p
  simp [ends,graft,edgeEnds,List.count_append,List.count_cons] <;> omega

theorem retained_ends (st : State) (row : RawVertex) :
    (ends {st with body := row::st.body}).Perm (row.2++ends st) := by
  apply List.perm_iff_count.mpr
  intro p
  simp [ends,List.count_append,List.count_cons] <;> omega

theorem expand_partition (s j4 m : ℕ) (rows : List RawVertex)
    (hw : ∀row∈rows,row.1=s → row.2.length=2) :
    (ends (expand s j4 m rows)).Perm
      (rows.flatMap Prod.snd++edgeEnds m (1+count s rows)) := by
  induction rows with
  | nil => simp [expand,ends,edgeEnds]
  | cons row rows ih =>
      have iht := ih (fun u hu => hw u (List.mem_cons_of_mem _ hu))
      by_cases h : row.1=s
      · have hp := graft_ends j4 (expand s j4 m rows) row.2 (hw row (by simp) h)
        have ht := (List.Perm.refl row.2).append
          (iht.append (List.Perm.refl (edgeEnds (expand s j4 m rows).next 1)))
        have he : 1+count s (row::rows)=(1+count s rows)+1 := by
          rw [count_cons,ite_eq_left h]; omega
        have hp' : (ends (graft j4 (expand s j4 m rows) row.2)).Perm
            (row.2++(ends (expand s j4 m rows)++edgeEnds (expand s j4 m rows).next 1)) := by
          simpa only [List.append_assoc] using hp
        simpa only [expand,if_pos h,List.flatMap_cons,he,edgeEnds_add,expand_next,
          List.append_assoc,Nat.add_assoc] using hp'.trans ht
      · simpa [expand,h,count_cons,List.append_assoc] using
          (retained_ends (expand s j4 m rows) row).trans ((List.Perm.refl row.2).append iht)

theorem expand_labels {s : ℕ} {a : ℕ → ℕ} (j4 : Fin s) (h4 : a j4.val=4)
    (m : ℕ) (rows : List RawVertex)
    (hw : ∀row∈rows,row.1<s+1 ∧ row.2.length=extendedArity s a row.1) :
    ∀row∈(expand s j4.val m rows).body,row.1<s ∧ row.2.length=a row.1 := by
  induction rows with
  | nil => simp [expand]
  | cons row rows ih =>
      have iht := ih (fun u hu => hw u (List.mem_cons_of_mem _ hu))
      have hr := hw row (by simp)
      by_cases h : row.1=s
      · intro u hu
        simp only [expand,if_pos h,graft,List.mem_cons] at hu
        rcases hu with rfl|hu
        · exact ⟨j4.isLt,by simpa using h4.symm⟩
        · exact iht _ hu
      · have hlt : row.1<s := by omega
        intro u hu
        simp only [expand,if_neg h,List.mem_cons] at hu
        rcases hu with rfl|hu
        · exact ⟨hlt,by simpa [extendedArity,hlt] using hr.2⟩
        · exact iht _ hu

theorem valid {s : ℕ} {a : ℕ → ℕ} (j4 : Fin s) (h4 : a j4.val=4) (r : Input s a) :
    (raw s j4.val r.val).WellFormed (s+1) 1 (extendedArity s a) := by
  have hr := (Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  have hl := expand_labels j4 h4 r.val.edges.length r.val.vertices hr.1
  apply (Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping.wellFormed_iff_members _ _ _ _).mpr
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
  · have hp := expand_partition s j4.val r.val.edges.length r.val.vertices (by
      intro row hm he
      simpa [extendedArity,he] using (hr.1 row hm).2)
    have ho : (r.val.vertices.flatMap Prod.snd).Perm (edgeEnds 0 r.val.edges.length) := by
      simpa [RawClosedNetwork.endpoints,expectedEndpoints_eq,List.flatMap] using hr.2.2
    have hf := hp.trans (ho.append (List.Perm.refl (edgeEnds r.val.edges.length (1+count s r.val.vertices))))
    simpa [raw,emitted,ends,RawClosedNetwork.endpoints,expectedEndpoints_eq,
      edgeEnds_add,List.flatMap,Nat.add_assoc] using hf

theorem one_carrier {s : ℕ} {a : ℕ → ℕ} (j4 : Fin s) (h4 : a j4.val=4) (r : Input s a) :
    FixedGadgetSubstitution.occurrences s (raw s j4.val r.val)=1 := by
  have hr := (Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  have hl := expand_labels j4 h4 r.val.edges.length r.val.vertices hr.1
  have hn : ((expand s j4.val r.val.edges.length r.val.vertices).body.filter
      (fun row => row.1==s))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro row hm
    simp [Nat.ne_of_lt (hl row hm).1]
  simp [FixedGadgetSubstitution.occurrences,raw,emitted,hn]

def query {s : ℕ} {a : ℕ → ℕ} (j4 : Fin s) (h4 : a j4.val=4) (r : Input s a) :
    UniversalPairReduction.Input s a :=
  ⟨raw s j4.val r.val,valid j4 h4 r,by rw [one_carrier j4 h4 r]⟩

/-- The scalar carrier is not discarded on empty input. -/
theorem empty_raw (s j4 : ℕ) : raw s j4 ⟨[],[]⟩=
    ⟨[(s,[(0,false),(0,true)])],[0]⟩ := rfl

/-- Extra Eq4 resources are exactly k. Pre-existing occurrences at this
same old index remain present and are charged as well. -/
theorem eq4_body_count (s j4 m : ℕ) (hne : j4≠s) (rows : List RawVertex) :
    count j4 (expand s j4 m rows).body=count j4 rows+count s rows := by
  induction rows with
  | nil => simp [expand,count,QuaternaryReplicationMachine.count]
  | cons row rows ih =>
      by_cases h : row.1=s
      · have hn : row.1≠j4 := by rw [h]; exact hne.symm
        simp [expand,h,graft,count_cons,hn,hne,hne.symm,ih] <;> omega
      · simp [expand,h,count_cons,ih] <;> omega

theorem raw_eq4_count {s : ℕ} (j4 : Fin s) (r : RawClosedNetwork) :
    count j4.val (raw s j4.val r).vertices=count j4.val r.vertices+count s r.vertices := by
  simpa [raw,emitted,count_cons,Nat.ne_of_lt j4.isLt,
    (Nat.ne_of_lt j4.isLt).symm] using
    eq4_body_count s j4.val r.edges.length (Nat.ne_of_lt j4.isLt) r.vertices

namespace EqChoice
abbrev Table := Surgery.Choice.Table
abbrev extend {m : ℕ} (c : Fin m → Bool) (i : ℕ) : Bool :=
  Surgery.Choice.extend (m:=m) c i
def bit (c : ℕ → Bool) (p : RawEndpoint) := c p.1
def rowValue {K : Type*} (T : Table K) (c : ℕ → Bool) (row : RawVertex) :=
  T row.1 (row.2.map (bit c))
def weight {K : Type*} [CommSemiring K] (T : Table K) (c : ℕ → Bool) (rows : List RawVertex) :=
  (rows.map (rowValue T c)).prod
def evaluate {K : Type*} [CommSemiring K] (T : Table K) (m : ℕ) (rows : List RawVertex) :=
  ∑c : Fin m → Bool,weight T (extend c) rows

theorem assigned_port {s : ℕ} {a : ℕ → ℕ}
    (r : RawClosedNetwork) (hr : r.WellFormed s 1 a) (c : Fin r.edges.length → Bool)
    (v : Fin r.vertices.length) (i : Fin (a (r.vertices.get v).1)) :
    (r.shape hr).assignment Fin.elim0 (fun p => c p.1) v i=
      ((r.vertices.get v).2.map (bit (extend c))).getD i.val false := by
  have hi : i.val<(r.vertices.get v).2.length := by rw [(hr.1 v).2]; exact i.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map]
  have he := r.portEndpoint_bound hr ⟨v,i⟩
  change c (r.route hr ⟨v,i⟩).1=_
  simp only [route,bit,extend,Surgery.Choice.extend,portEndpoint,List.get_eq_getElem,Fin.val_cast] at he ⊢
  simp only [dif_pos he]

/-- Actual Eq half-edge sum, retaining both sides of a self-loop in the
incidence while equality identifies their values. -/
theorem denote_eq_evaluate {K : Type*} [CommSemiring K] {s : ℕ} {a : ℕ → ℕ}
    (r : RawClosedNetwork) (hr : r.WellFormed s 1 a)
    (G : (i : Fin s) → Signature K (a i.val)) :
    (r.realize hr G (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0=
      evaluate (Surgery.Choice.table G) r.edges.length r.vertices := by
  change (Network.mk (r.shape hr) _ (fun _ => Signature.equality)).denote Fin.elim0=_
  rw [Network.denote_equality]
  unfold Network.ordinaryDenote evaluate weight
  apply Finset.sum_congr rfl
  intro c _
  rw [←List.prod_ofFn,←List.ofFn_getElem_eq_map r.vertices]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext v
  change G (r.signatureLabel hr v) _=rowValue (Surgery.Choice.table G) (extend c) (r.vertices.get v)
  unfold rowValue Surgery.Choice.table
  rw [dif_pos (hr.1 v).1]
  congr 1
  funext i
  exact assigned_port r hr c v i

theorem row_put_old {K : Type*} (T : Table K) (c : ℕ → Bool) (e : ℕ)
    (b : Bool) (row : RawVertex) (h : ∀p∈row.2,p.1<e) :
    rowValue T (QuaternaryReplicationMachine.put c e b) row=rowValue T c row := by
  unfold rowValue
  congr 1
  apply List.map_congr_left
  intro p hp
  simp [bit,QuaternaryReplicationMachine.put,Nat.ne_of_lt (h p hp)]
theorem weight_put_old {K : Type*} [CommSemiring K] (T : Table K)
    (c : ℕ → Bool) (e : ℕ) (b : Bool) (rows : List RawVertex)
    (h : ∀row∈rows,∀p∈row.2,p.1<e) :
    weight T (QuaternaryReplicationMachine.put c e b) rows=weight T c rows := by
  unfold weight
  congr 1
  exact List.map_congr_left (fun row hr => row_put_old T c e b row (h row hr))
theorem weight_cons {K : Type*} [CommSemiring K] (T : Table K)
    (c : ℕ → Bool) (row : RawVertex) (rows : List RawVertex) :
    weight T c (row::rows)=rowValue T c row*weight T c rows := rfl
end EqChoice

/- This section consumes the existing Type-0 fixed-field ordinary companion
API. Raw graph composition and the generic EqChoice semiring semantics above
retain their original universe-polymorphic scope. -/
section Semantics
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))
variable (j4 : Fin s)
variable (h4 : (⟨a j4.val,G j4⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (j : Bool)

def pinPair : BinaryTable K := fun b c => (if b=j then 1 else 0)*(if c=j then 1 else 0)
theorem pinPair_nonzero : (fun x : Fin 2 → Bool => pinPair (K:=K) j (x 0) (x 1))≠0 := by
  intro h
  have hh := congrFun h (fun _ => j)
  simp [pinPair] at hh

/-- Exact unrestricted source palette, including coincident signatures
and repeated labels. This is a table identity, not a realizability claim. -/
theorem source_family_exact :
    Set.range (fun i : Fin (s+1) => (⟨extendedArity s a i.val,
      BinaryFamily.signatures G (pinPair (K:=K) j) i⟩ : AnySignature K))=
      Set.range (fun i : Fin s => (⟨a i.val,G i⟩ : AnySignature K)) ∪
        {(⟨2,fun x => pinPair (K:=K) j (x 0) (x 1)⟩ : AnySignature K)} :=
  EdgeSubdivision.extended_family G (pinPair (K:=K) j)

def sourceValue (r : Input s a) : K :=
  (r.val.realize r.property (BinaryFamily.signatures G (pinPair (K:=K) j))
    (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0
abbrev sourceTable := Surgery.Choice.table (BinaryFamily.signatures G (pinPair (K:=K) j))
abbrev carrierTable := Surgery.Choice.table (BinaryFamily.signatures G (QuaternaryOrdinaryCompanion.pair G j))

theorem table_old (B : BinaryTable K) (i : ℕ) (hi : i<s) (bits : List Bool) :
    Surgery.Choice.table (BinaryFamily.signatures G B) i bits=Surgery.Choice.table G i bits :=
  BinaryFamily.table_old G B i hi bits
theorem table_new (B : BinaryTable K) (bits : List Bool) :
    Surgery.Choice.table (BinaryFamily.signatures G B) s bits=
      B (bits.getD 0 false) (bits.getD 1 false) := BinaryFamily.table_new G B bits

include h4 in
theorem eq4_table (b0 b1 b2 b3 : Bool) :
    Surgery.Choice.table (BinaryFamily.signatures G (QuaternaryOrdinaryCompanion.pair G j))
      j4.val [b0,b1,b2,b3]=
      Holant.EightVertex.ProductAnchor.equalityFour ![b0,b1,b2,b3] := by
  rw [table_old G (QuaternaryOrdinaryCompanion.pair G j) j4.val j4.isLt]
  unfold Surgery.Choice.table
  rw [dif_pos j4.isLt]
  have h := BinaryInterpolation.Chains.signature_cast_apply (G j4)
    Holant.EightVertex.ProductAnchor.equalityFour h4 (congrArg Sigma.fst h4) ![b0,b1,b2,b3]
  rw [←h]
  congr 1
  funext i
  have ha : a j4.val = 4 := congrArg Sigma.fst h4
  have hi : i.val<4 := by
    have hib : i.val < a j4.val := i.isLt
    omega
  have hv (t : Fin 4) : [b0,b1,b2,b3].getD t.val false=(![b0,b1,b2,b3] : Fin 4 → Bool) t := by
    fin_cases t <;> rfl
  exact hv ⟨i.val,hi⟩

/-- Local ordered contraction: ONE newly allocated Eq edge, no independence
assumption on the old two ports (which can be ends of the same old edge). -/
theorem local_contraction (z0 z1 x0 x1 : Bool) :
    (∑u : Bool,QuaternaryOrdinaryCompanion.pair G j u z1 *
      Holant.EightVertex.ProductAnchor.equalityFour ![u,z0,x0,x1])=
      pinPair (K:=K) j x0 x1*QuaternaryOrdinaryCompanion.pair G j z0 z1 := by
  cases j <;> cases z0 <;> cases z1 <;> cases x0 <;> cases x1 <;>
    simp [QuaternaryOrdinaryCompanion.pair,QuaternaryOrdinaryCompanion.companion,pinPair,Holant.EightVertex.ProductAnchor.equalityFour,
      Fin.forall_fin_succ,Fintype.sum_bool]

include h4 in
theorem graft_sum (st : State) (L : List RawEndpoint) (hL : L.length=2)
    (hs : ∀p∈ends st,p.1<st.next) (hB : ∀p∈L,p.1<st.next) (c : ℕ → Bool) :
    (∑u : Bool,EqChoice.weight (carrierTable G j) (QuaternaryReplicationMachine.put c st.next u)
      (emitted s (graft j4.val st L)))=
      EqChoice.rowValue (sourceTable G j) c (s,L)*
        EqChoice.weight (carrierTable G j) c (emitted s st) := by
  have hz := hs st.carrierPort (by simp [ends])
  have ho := hs st.otherPort (by simp [ends])
  have hbody : ∀row∈st.body,∀p∈row.2,p.1<st.next := by
    intro row hr p hp
    exact hs p (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row,hr,hp⟩)))
  have hports := two_ports L hL
  obtain ⟨p0,p1,hports'⟩ : ∃p0 p1,L=[p0,p1] := ⟨_,_,hports⟩
  subst L
  have hb0 := hB p0 (by simp)
  have hb1 := hB p1 (by simp)
  have term (u : Bool) : EqChoice.weight (carrierTable G j) (QuaternaryReplicationMachine.put c st.next u)
      (emitted s (graft j4.val st [p0,p1]))=
      (QuaternaryOrdinaryCompanion.pair G j u (EqChoice.bit c st.otherPort)*
        Holant.EightVertex.ProductAnchor.equalityFour
          ![u,EqChoice.bit c st.carrierPort,EqChoice.bit c p0,EqChoice.bit c p1])*
        EqChoice.weight (carrierTable G j) c st.body := by
    simp only [emitted,graft,EqChoice.weight_cons,EqChoice.rowValue,List.map_cons,List.map_nil,
      List.getD_cons_zero,List.getD_cons_succ]
    rw [EqChoice.weight_put_old _ _ _ _ _ hbody]
    simp only [carrierTable,table_new]
    simp only [EqChoice.bit,QuaternaryReplicationMachine.put,if_true,Nat.ne_of_lt hz,Nat.ne_of_lt ho,
      Nat.ne_of_lt hb0,Nat.ne_of_lt hb1,if_false]
    rw [eq4_table G j4 h4 j]
    simp only [List.getD_cons_zero,List.getD_cons_succ,List.getD_nil]
    ring
  simp_rw [term]
  rw [←Finset.sum_mul,local_contraction]
  simp [EqChoice.rowValue,sourceTable,carrierTable,table_new,emitted,EqChoice.weight_cons,mul_assoc]

theorem expand_bound (s j4 m : ℕ) (rows : List RawVertex)
    (hw : ∀row∈rows,row.1=s → row.2.length=2)
    (hb : ∀row∈rows,∀p∈row.2,p.1<m) :
    ∀p∈ends (expand s j4 m rows),p.1<(expand s j4 m rows).next := by
  intro p hp
  have hh := (expand_partition s j4 m rows hw).mem_iff.mp hp
  rcases List.mem_append.mp hh with hh|hh
  · rcases List.mem_flatMap.mp hh with ⟨row,hr,hp⟩
    have h := hb row hr p hp
    rw [expand_next]; omega
  · have h := (Template.mem_edgeEnds m (1+count s rows) p).mp hh
    rw [expand_next]; omega

include h4 in
/-- All fresh edges are summed, with every original edge held fixed.
The empty tail closes its real carrier through Eq, producing d, not one. -/
theorem expand_fresh (m : ℕ) (rows : List RawVertex)
    (hw : ∀row∈rows,row.1<s+1 ∧ row.2.length=extendedArity s a row.1)
    (hb : ∀row∈rows,∀p∈row.2,p.1<m) (c : ℕ → Bool) :
    QuaternaryReplicationMachine.fresh m (1+count s rows)
      (fun d => EqChoice.weight (carrierTable G j) d (emitted s (expand s j4.val m rows))) c=
      QuaternaryOrdinaryCompanion.companion G j j*EqChoice.weight (sourceTable G j) c rows := by
  revert hw hb
  induction rows with
  | nil =>
      intro hw hb
      cases j <;> simp [count,QuaternaryReplicationMachine.count,expand,emitted,QuaternaryReplicationMachine.fresh,EqChoice.weight,EqChoice.rowValue,
        carrierTable,table_new,EqChoice.bit,QuaternaryReplicationMachine.put,QuaternaryOrdinaryCompanion.pair,QuaternaryOrdinaryCompanion.companion,Fintype.sum_bool]
  | cons row rows ih =>
      intro hw hb
      have hwt := fun u hu => hw u (List.mem_cons_of_mem _ hu)
      have hbt := fun u hu => hb u (List.mem_cons_of_mem _ hu)
      have hrow := hw row (by simp)
      have hrowb := hb row (by simp)
      have hpull (d : ℕ → Bool) (e : ℕ) (b : Bool) (he : m≤e) :
          EqChoice.rowValue (sourceTable G j) (QuaternaryReplicationMachine.put d e b) row=
            EqChoice.rowValue (sourceTable G j) d row :=
        EqChoice.row_put_old _ _ _ _ _ (fun p hp => (hrowb p hp).trans_le he)
      by_cases hh : row.1=s
      · have hlen : row.2.length=2 := by simpa [extendedArity,hh] using hrow.2
        have hroweq : (s,row.2)=row := Prod.ext hh.symm rfl
        have hn : 1+count s (row::rows)=(1+count s rows)+1 := by
          rw [count_cons,ite_eq_left hh]; omega
        have hs := expand_bound s j4.val m rows
          (fun u hu he => by simpa [extendedArity,he] using (hwt u hu).2) hbt
        have hnext := expand_next s j4.val m rows
        have hc (d : ℕ → Bool) := graft_sum G j4 h4 j (expand s j4.val m rows)
          row.2 hlen hs (fun p hp => by have := hrowb p hp; rw [hnext]; omega) d
        rw [hn]
        simp only [expand,if_pos hh,QuaternaryReplicationMachine.fresh]
        have heq := QuaternaryReplicationMachine.fresh_congr m (1+count s rows)
          (fun d => by simpa only [hnext,hroweq,Nat.add_assoc] using hc d) c
        rw [heq,QuaternaryReplicationMachine.fresh_pull m _ _ _ hpull,ih hwt hbt,EqChoice.weight_cons]
        ring
      · have hlt : row.1<s := by omega
        have hsame (d : ℕ → Bool) : EqChoice.rowValue (carrierTable G j) d row=
            EqChoice.rowValue (sourceTable G j) d row := by
          simp [EqChoice.rowValue,carrierTable,sourceTable,table_old,hlt]
        have heq (d : ℕ → Bool) :
            EqChoice.weight (carrierTable G j) d (emitted s (expand s j4.val m (row::rows)))=
              EqChoice.rowValue (sourceTable G j) d row*
                EqChoice.weight (carrierTable G j) d (emitted s (expand s j4.val m rows)) := by
          simp only [expand,if_neg hh,emitted,EqChoice.weight_cons]
          rw [hsame]
          ring
        have hn : count s (row::rows)=count s rows := by simp [count_cons,hh]
        rw [hn,QuaternaryReplicationMachine.fresh_congr _ _ heq,QuaternaryReplicationMachine.fresh_pull m _ _ _ hpull,ih hwt hbt,
          EqChoice.weight_cons]
        ring

include h4 in
/-- Global partition identity for the SAME raw query. No graph is chosen
by value, no freely available unary is introduced, and no component is dropped. -/
theorem query_value (r : Input s a) :
    QuaternaryOrdinaryCompanion.value G (QuaternaryOrdinaryCompanion.pair G j) (query j4 (congrArg Sigma.fst h4) r)=
      QuaternaryOrdinaryCompanion.companion G j j*sourceValue G j r := by
  have hr := (Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  have hb : ∀row∈r.val.vertices,∀p∈row.2,p.1<r.val.edges.length := by
    intro row hrow p hp
    have hm : p∈r.val.vertices.flatMap Prod.snd := List.mem_flatMap.mpr ⟨row,hrow,hp⟩
    have he : (r.val.vertices.flatMap Prod.snd).Perm (edgeEnds 0 r.val.edges.length) := by
      simpa [RawClosedNetwork.endpoints,expectedEndpoints_eq,List.flatMap] using hr.2.2
    exact (ends_mem _ _).mp (he.mem_iff.mp hm)
  unfold QuaternaryOrdinaryCompanion.value QuaternaryOrdinaryCompanion.network sourceValue
  rw [EqChoice.denote_eq_evaluate,EqChoice.denote_eq_evaluate]
  change EqChoice.evaluate (carrierTable G j) (raw s j4.val r.val).edges.length
    (emitted s (expand s j4.val r.val.edges.length r.val.vertices))=_
  rw [raw_edges,show r.val.edges.length+1+count s r.val.vertices=
    r.val.edges.length+(1+count s r.val.vertices) by omega]
  unfold EqChoice.evaluate
  change (∑ c : Fin (r.val.edges.length+(1+count s r.val.vertices)) → Bool,
    EqChoice.weight (carrierTable G j) (Surgery.Choice.extend c)
      (emitted s (expand s j4.val r.val.edges.length r.val.vertices))) = _
  rw [QuaternaryReplicationMachine.sum_fresh r.val.edges.length (1+count s r.val.vertices)
    (fun c => EqChoice.weight (carrierTable G j) c
      (emitted s (expand s j4.val r.val.edges.length r.val.vertices)))]
  simp_rw [expand_fresh G j4 h4 j _ _ hr.1 hb]
  rw [Finset.mul_sum]

end Semantics
end Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication
