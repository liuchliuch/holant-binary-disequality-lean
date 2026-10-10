import Holant.Network
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Nodup
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.ValiantXor
open Holant
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
local instance : Fintype Bool := Bool.fintype

abbrev Vertex := Fin 4
abbrev Word := Fin 4 → Bool
abbrev Edge := Vertex × Vertex

/-- Row first, column second. Zero entries remain literal zero weights. -/
def matrix : Vertex → Vertex → ℤ :=
  ![![0,0,1,0],![0,0,0,1],![-1,1,1,1],![1,1,1,-1]]

/-- All internal row/column pairs, in row-major order. -/
def internalEdges : List Edge :=
  [(0,0),(0,1),(0,2),(0,3),
   (1,0),(1,1),(1,2),(1,3),
   (2,0),(2,1),(2,2),(2,3),
   (3,0),(3,1),(3,2),(3,3)]

/-- The ten actual nonzero-weight edges. Absent entries of the matrix are
zero, and their matching contributions will be removed by a proved sum law.
-/
def activeEdges : List Edge :=
  [(0,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)]

/-- False denotes the incoming/row side, true the outgoing/column side. -/
def boundaryVertex : Fin 4 → Bool × Vertex :=
  ![(false,0),(false,1),(true,0),(true,1)]

structure MatchingTemplate where
  edges : List Edge
  weight : Edge → ℤ
  boundary : Fin 4 → Bool × Vertex

/-- The fixed finite graph, all its integer edge weights, and all four
external incidences. A true boundary bit already matches that vertex outside.
-/
def template : MatchingTemplate :=
  ⟨activeEdges,fun e => matrix e.1 e.2,boundaryVertex⟩

theorem internal_edges_complete (e : Edge) : e ∈ internalEdges := by
  rcases e with ⟨r,c⟩
  fin_cases r <;> fin_cases c <;> decide

theorem template_edges_exact (e : Edge) : e ∈ template.edges ↔ matrix e.1 e.2≠0 := by
  rcases e with ⟨r,c⟩
  fin_cases r <;> fin_cases c <;> decide

theorem template_edges_nodup : template.edges.Nodup := by decide
theorem template_weights (e : Edge) :
    template.weight e=-1 ∨ template.weight e=0 ∨ template.weight e=1 := by
  rcases e with ⟨r,c⟩
  fin_cases r <;> fin_cases c <;> decide
theorem template_boundary : template.boundary=
    ![(false,0),(false,1),(true,0),(true,1)] := rfl

def indices : List Vertex := [0,1,2,3]
def rowOccupied (t : Word) (r : Vertex) : Bool :=
  if r=0 then t 0 else if r=1 then t 1 else false
def columnOccupied (t : Word) (c : Vertex) : Bool :=
  if c=0 then t 2 else if c=1 then t 3 else false
def rows (t : Word) : List Vertex := indices.filter (fun r => !rowOccupied t r)
def columns (t : Word) : List Vertex := indices.filter (fun c => !columnOccupied t c)

def bitNat (b : Bool) : ℕ := if b then 1 else 0
def incomingCount (t : Word) : ℕ := bitNat (t 0)+bitNat (t 1)
def outgoingCount (t : Word) : ℕ := bitNat (t 2)+bitNat (t 3)

theorem word_eta (t : Word) : ![t 0,t 1,t 2,t 3]=t := by
  funext i
  fin_cases i <;> rfl

theorem rows_nodup (t : Word) : (rows t).Nodup :=
  List.Nodup.filter _ (by decide : indices.Nodup)
theorem columns_nodup (t : Word) : (columns t).Nodup :=
  List.Nodup.filter _ (by decide : indices.Nodup)

theorem rows_exactly_once (t : Word) (r : Vertex) :
    (rows t).count r+bitNat (rowOccupied t r)=1 := by
  fin_cases r <;> cases h0 : t 0 <;> cases h1 : t 1 <;>
    simp [rows,indices,rowOccupied,bitNat,h0,h1]
theorem columns_exactly_once (t : Word) (c : Vertex) :
    (columns t).count c+bitNat (columnOccupied t c)=1 := by
  fin_cases c <;> cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [columns,indices,columnOccupied,bitNat,h2,h3]

theorem balanced_iff (t : Word) :
    (rows t).length=(columns t).length ↔ incomingCount t=outgoingCount t := by
  cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [rows,columns,indices,rowOccupied,columnOccupied,incomingCount,outgoingCount,bitNat,h0,h1,h2,h3]

/-- A matching is a permutation of the available columns, paired with the
fixed available-row order. Unequal cardinalities have no matching at all.
-/
def completions (t : Word) : List (List Vertex) :=
  if (rows t).length=(columns t).length then (columns t).permutations else []
def completionEdges (t : Word) (cs : List Vertex) : List Edge := (rows t).zip cs
def completionWeight (t : Word) (cs : List Vertex) : ℤ :=
  ((completionEdges t cs).map (fun e => matrix e.1 e.2)).prod

theorem completion_spec (t : Word) (cs : List Vertex) :
    cs ∈ completions t ↔ cs.Perm (columns t) ∧ (rows t).length=cs.length := by
  unfold completions
  by_cases h : (rows t).length=(columns t).length
  · rw [if_pos h,List.mem_permutations]
    constructor
    · intro hp
      exact ⟨hp,h.trans hp.length_eq.symm⟩
    · exact And.left
  · rw [if_neg h]
    constructor
    · intro hm
      cases hm
    · rintro ⟨hp,hl⟩
      exact False.elim (h (hl.trans hp.length_eq))

theorem completions_nodup (t : Word) : (completions t).Nodup := by
  unfold completions
  split
  · exact List.nodup_permutations _ (columns_nodup t)
  · exact List.nodup_nil

private theorem zip_maps {α β : Type} (rs : List α) (cs : List β)
    (h : rs.length=cs.length) :
    (rs.zip cs).map Prod.fst=rs ∧ (rs.zip cs).map Prod.snd=cs := by
  induction rs generalizing cs with
  | nil =>
    cases cs with
    | nil => exact ⟨rfl,rfl⟩
    | cons c cs => simp at h
  | cons r rs ih =>
    cases cs with
    | nil => simp at h
    | cons c cs =>
      obtain ⟨hf,hs⟩ := ih cs (by simpa using h)
      constructor <;> simp [hf,hs]

private theorem zip_of_maps {α β : Type} (es : List (α × β)) :
    (es.map Prod.fst).zip (es.map Prod.snd)=es := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa using congrArg (List.cons e) ih

theorem completion_maps (t : Word) (cs : List Vertex) (h : cs ∈ completions t) :
    (completionEdges t cs).map Prod.fst=rows t ∧
    (completionEdges t cs).map Prod.snd=cs :=
  zip_maps _ _ ((completion_spec t cs).mp h).2

/-- Exact-one at EVERY vertex, including the occupied external endpoints.
This concerns the actual selected internal edges, not just boundary support.
-/
theorem completion_exact_one (t : Word) (cs : List Vertex) (h : cs ∈ completions t) :
    (∀ r,((completionEdges t cs).map Prod.fst).count r+bitNat (rowOccupied t r)=1) ∧
    (∀ c,((completionEdges t cs).map Prod.snd).count c+bitNat (columnOccupied t c)=1) := by
  obtain ⟨hf,hs⟩ := completion_maps t cs h
  have hp := ((completion_spec t cs).mp h).1
  constructor
  · intro r
    rw [hf]
    exact rows_exactly_once t r
  · intro c
    rw [hs,hp.count_eq]
    exact columns_exactly_once t c

/-- Canonical row order; permutation of columns is the ordinary bipartite
matching condition. No port or internally matched vertex is omitted.
-/
def LegalMatching (t : Word) (es : List Edge) : Prop :=
  es.map Prod.fst=rows t ∧ (es.map Prod.snd).Perm (columns t)

theorem completion_legal (t : Word) (cs : List Vertex) (h : cs ∈ completions t) :
    LegalMatching t (completionEdges t cs) := by
  obtain ⟨hf,hs⟩ := completion_maps t cs h
  exact ⟨hf,by rw [hs]; exact ((completion_spec t cs).mp h).1⟩

/-- Every canonically ordered complete internal matching is enumerated
exactly once. Thus the partition below is a sum over real local matchings.
-/
theorem matching_complete (t : Word) (es : List Edge) (h : LegalMatching t es) :
    ∃! cs, cs ∈ completions t ∧ completionEdges t cs=es := by
  let cs := es.map Prod.snd
  have hl : (rows t).length=cs.length := by
    rw [← h.1]
    simp [cs]
  have hm : cs ∈ completions t := (completion_spec t cs).mpr ⟨h.2,hl⟩
  have he : completionEdges t cs=es := by
    change (rows t).zip (es.map Prod.snd)=es
    rw [← h.1]
    exact zip_of_maps es
  refine ⟨cs,⟨hm,he⟩,?_⟩
  rintro other ⟨ho,heq⟩
  have hh := congrArg (List.map Prod.snd) heq
  exact (completion_maps t other ho).2.symm.trans hh

/-- The open weighted matching tensor: ALL internal complete matchings,
including negative contributions and choices using a zero-weight edge.
-/
def tensor (t : Word) : ℤ := ((completions t).map (completionWeight t)).sum

def active (t : Word) (cs : List Vertex) : Bool :=
  (completionEdges t cs).all (fun e => decide (matrix e.1 e.2≠0))
def actualCompletions (t : Word) : List (List Vertex) := (completions t).filter (active t)
def actualTensor (t : Word) : ℤ := ((actualCompletions t).map (completionWeight t)).sum

private theorem zero_product (es : List Edge)
    (h : es.all (fun e => decide (matrix e.1 e.2≠0))=false) :
    (es.map (fun e => matrix e.1 e.2)).prod=0 := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    by_cases he : matrix e.1 e.2=0
    · simp [he]
    · have ht : es.all (fun e => decide (matrix e.1 e.2≠0))=false := by
        simpa [he] using h
      simp [ih ht]

private theorem sum_filter_zero {α : Type} (p : α → Bool) (f : α → ℤ)
    (hf : ∀ a,p a=false → f a=0) (xs : List α) :
    ((xs.filter p).map f).sum=(xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : p a
    · simp [h,hf a h,ih]
    · simp [h,ih]

/-- The actual ten-edge graph has exactly the same signature as the
matrix-permanent sum: every omitted zero-edge choice contributes zero.
-/
theorem actual_tensor_eq (t : Word) : actualTensor t=tensor t := by
  exact sum_filter_zero (active t) (completionWeight t)
    (fun cs h => zero_product (completionEdges t cs) h) (completions t)

theorem actual_matching_edges (t : Word) (cs : List Vertex) (h : cs ∈ actualCompletions t)
    (e : Edge) (he : e ∈ completionEdges t cs) : e ∈ template.edges := by
  have ha := (List.mem_filter.mp h).2
  exact (template_edges_exact e).mpr (of_decide_eq_true ((List.all_eq_true.mp ha) e he))

theorem actual_matching_exact_one (t : Word) (cs : List Vertex)
    (h : cs ∈ actualCompletions t) :
    (∀ r,((completionEdges t cs).map Prod.fst).count r+bitNat (rowOccupied t r)=1) ∧
    (∀ c,((completionEdges t cs).map Prod.snd).count c+bitNat (columnOccupied t c)=1) :=
  completion_exact_one t cs (List.mem_filter.mp h).1

theorem actual_completions_nodup (t : Word) : (actualCompletions t).Nodup :=
  List.Nodup.filter _ (completions_nodup t)

theorem actual_matching_complete (t : Word) (es : List Edge) (h : LegalMatching t es)
    (hedges : ∀ e ∈ es,e ∈ template.edges) :
    ∃! cs,cs ∈ actualCompletions t ∧ completionEdges t cs=es := by
  obtain ⟨cs,⟨hc,heq⟩,hu⟩ := matching_complete t es h
  have ha : active t cs=true := by
    apply List.all_eq_true.mpr
    intro e he
    have hn := (template_edges_exact e).mp (hedges e (by simpa only [heq] using he))
    simpa using hn
  refine ⟨cs,⟨List.mem_filter.mpr ⟨hc,ha⟩,heq⟩,?_⟩
  rintro other ⟨ho,he⟩
  exact hu other ⟨(List.mem_filter.mp ho).1,he⟩

/-- Degree includes the retained external edge at vertices 0 and 1. Only
the two incoming internal vertices have degree four; every column has three.
-/
def rowDegree (r : Vertex) : ℕ := (activeEdges.map Prod.fst).count r+if r<2 then 1 else 0
def columnDegree (c : Vertex) : ℕ := (activeEdges.map Prod.snd).count c+if c<2 then 1 else 0
theorem row_degrees (r : Vertex) : rowDegree r=![2,2,4,4] r := by fin_cases r <;> decide
theorem column_degrees (c : Vertex) : columnDegree c=3 := by fin_cases c <;> decide

theorem unbalanced_no_matching (t : Word) (h : incomingCount t≠outgoingCount t) :
    completions t=[] := by
  unfold completions
  exact if_neg (fun hl => h ((balanced_iff t).mp hl))
theorem unbalanced_zero (t : Word) (h : incomingCount t≠outgoingCount t) : tensor t=0 := by
  simp [tensor,unbalanced_no_matching t h]

/-- Exactly one paired connection: either incoming 0 with outgoing 0, or
incoming 1 with outgoing 1, and NONE of the other two external occupations.
-/
def paired (t : Word) : Bool :=
  (t 0 && !t 1 && t 2 && !t 3) || (!t 0 && t 1 && !t 2 && t 3)

/-- Kernel evaluation of the concrete list of at most 24 matchings. The
16 cases contain full/empty, both cross minors, and all unbalanced patterns.
-/
theorem literal_tensor (a b c d : Bool) :
    tensor ![a,b,c,d]=if paired ![a,b,c,d] then 2 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [tensor,completions,rows,columns,indices,rowOccupied,columnOccupied,completionWeight,completionEdges,matrix,paired,List.permutations,List.permutationsAux_cons,List.permutationsAux_nil,List.permutationsAux2]

theorem tensor_exact (t : Word) : tensor t=if paired t then 2 else 0 := by
  simpa only [word_eta] using literal_tensor (t 0) (t 1) (t 2) (t 3)

theorem paired_iff (t : Word) : paired t=true ↔
    (t 0=true ∧ t 1=false ∧ t 2=true ∧ t 3=false) ∨
    (t 0=false ∧ t 1=true ∧ t 2=false ∧ t 3=true) := by
  cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [paired,h0,h1,h2,h3]

theorem actual_tensor_exact (t : Word) : actualTensor t=if paired t then 2 else 0 := by
  rw [actual_tensor_eq,tensor_exact]

/-- Explicit lexicographic ordering of all four-port words, 0000 to 1111. -/
def words : Fin 16 → Word :=
  ![![false,false,false,false],![false,false,false,true],
    ![false,false,true,false],![false,false,true,true],
    ![false,true,false,false],![false,true,false,true],
    ![false,true,true,false],![false,true,true,true],
    ![true,false,false,false],![true,false,false,true],
    ![true,false,true,false],![true,false,true,true],
    ![true,true,false,false],![true,true,false,true],
    ![true,true,true,false],![true,true,true,true]]
def orderedTable : Fin 16 → ℤ := ![0,0,0,0,0,2,0,0,0,0,2,0,0,0,0,0]
theorem full_ordered_table (i : Fin 16) : tensor (words i)=orderedTable i := by
  rw [tensor_exact]
  fin_cases i <;> decide

theorem full_permanent : tensor ![false,false,false,false]=0 := by rw [tensor_exact]; decide
theorem two_rows_two_columns_deleted : tensor ![true,true,true,true]=0 := by rw [tensor_exact]; decide
theorem first_paired_minor : tensor ![true,false,true,false]=2 := by rw [tensor_exact]; decide
theorem second_paired_minor : tensor ![false,true,false,true]=2 := by rw [tensor_exact]; decide
theorem first_cross_minor : tensor ![true,false,false,true]=0 := by rw [tensor_exact]; decide
theorem second_cross_minor : tensor ![false,true,true,false]=0 := by rw [tensor_exact]; decide

/-- Actual nonzero matchings responsible for the two cancelling full terms.
No other nonzero internal choice is hidden by the permanent notation. -/
theorem full_choices : (actualCompletions ![false,false,false,false]).Perm
    [[2,3,0,1],[2,3,1,0]] := by
  norm_num [actualCompletions, completions, rows, columns, indices, rowOccupied, columnOccupied, completionWeight, completionEdges, matrix, List.permutations, List.permutationsAux_cons, List.permutationsAux_nil, List.permutationsAux2]
  decide
theorem full_negative_term : completionWeight ![false,false,false,false] [2,3,0,1]=-1 := by decide
theorem full_positive_term : completionWeight ![false,false,false,false] [2,3,1,0]=1 := by decide
theorem double_choices : (actualCompletions ![true,true,true,true]).Perm [[2,3],[3,2]] := by
  norm_num [actualCompletions, completions, rows, columns, indices, rowOccupied, columnOccupied, completionWeight, completionEdges, matrix, List.permutations, List.permutationsAux_cons, List.permutationsAux_nil, List.permutationsAux2]
  decide
theorem double_negative_term : completionWeight ![true,true,true,true] [2,3]=-1 := by decide
theorem double_positive_term : completionWeight ![true,true,true,true] [3,2]=1 := by decide

def bottom : Fin 2 → Fin 2 → ℤ := ![![1,1],![1,-1]]
def lowerLeft : Fin 2 → Fin 2 → ℤ := ![![-1,1],![1,1]]
def upperRight : Fin 2 → Fin 2 → ℤ := ![![1,0],![0,1]]
def permanentTwo (a : Fin 2 → Fin 2 → ℤ) : ℤ := a 0 0*a 1 1+a 0 1*a 1 0
theorem bottom_cancellation : permanentTwo bottom=0 := by decide
theorem lower_left_cancellation : permanentTwo lowerLeft=0 := by decide

theorem matrix_blocks (r c : Fin 2) :
    matrix (Fin.castAdd 2 r) (Fin.castAdd 2 c)=0 ∧
    matrix (Fin.castAdd 2 r) (Fin.natAdd 2 c)=upperRight r c ∧
    matrix (Fin.natAdd 2 r) (Fin.castAdd 2 c)=lowerLeft r c ∧
    matrix (Fin.natAdd 2 r) (Fin.natAdd 2 c)=bottom r c := by
  fin_cases r <;> fin_cases c <;> decide

/-- Permanental cofactors of the literal bottom block, in the order used
by an incoming-to-outgoing path. The four single-minor values are derived
from the actual matching sum, not supplied as a gate equation. -/
def cofactor : Fin 2 → Fin 2 → ℤ := ![![-1,1],![1,1]]
def pathCoefficient (r c : Fin 2) : ℤ :=
  ∑ j : Fin 2, ∑ k : Fin 2, upperRight r j*cofactor j k*lowerLeft k c
def singleMinor (r c : Fin 2) : ℤ :=
  tensor ![decide (r=0),decide (r=1),decide (c=0),decide (c=1)]
theorem single_minor_factorization (r c : Fin 2) : singleMinor r c=pathCoefficient r c := by
  simp only [singleMinor, tensor_exact, pathCoefficient,Fin.sum_univ_two]
  fin_cases r <;> fin_cases c <;> decide
theorem path_coefficient (r c : Fin 2) : pathCoefficient r c=if r=c then 2 else 0 := by
  simp only [pathCoefficient,Fin.sum_univ_two]
  fin_cases r <;> fin_cases c <;> decide

/-- The same matching sum with these literal integer weights cast to a ring.
This is algebraic transport, not an original-M resource-access assertion.
-/
def tensorOver (K : Type*) [Ring K] (t : Word) : K :=
  ((completions t).map (fun cs =>
    ((completionEdges t cs).map (fun e => (matrix e.1 e.2 : K))).prod)).sum
theorem tensorOver_cast (K : Type*) [Ring K] (t : Word) : tensorOver K t=(tensor t : K) := by
  simp [tensorOver,tensor,completionWeight,Int.cast_list_sum,Int.cast_list_prod,
    List.map_map,Function.comp_def]
theorem tensorOver_exact (K : Type*) [Ring K] (t : Word) :
    tensorOver K t=if paired t then 2 else 0 := by
  rw [tensorOver_cast,tensor_exact]
  cases h : paired t <;> simp [h]
theorem scalar_nonzero (K : Type*) [Field K] [CharZero K] : (2 : K)≠0 := by norm_num
theorem scalar_correction (K : Type*) [Field K] [CharZero K] (t : Word) :
    tensorOver K t*(2 : K)⁻¹=if paired t then 1 else 0 := by
  rw [tensorOver_exact]
  cases h : paired t <;> simp [h,scalar_nonzero K]

namespace DegreeFour

/-- Ordinary unit matching tensor at a vertex of any finite degree. -/
def exactOne (n : ℕ) : Signature ℤ n := fun t =>
  if (List.ofFn t).count true=1 then 1 else 0

/-- Two vertices on the original side, with one opposite-side degree-two
vertex between them. The two path edges are ordinary unit matching edges.
External ports 0,1 belong to the first endpoint and 2,3 to the second.
-/
abbrev shape : NetworkShape 4 where
  vertices := 3
  arity v := if v=2 then 2 else 3
  edges := 2
  ports := {
    toFun := fun p => if h : p.1=2 then
      ![Sum.inr (0,true),Sum.inr (1,true)] (Fin.cast (by simp [h]) p.2)
      else if h0 : p.1=0 then
        ![Sum.inl 0,Sum.inl 1,Sum.inr (0,false)] (Fin.cast (by simp [h]) p.2)
      else ![Sum.inl 2,Sum.inl 3,Sum.inr (1,false)] (Fin.cast (by simp [h]) p.2)
    invFun := fun p => match p with
      | .inl i => ![⟨0,0⟩,⟨0,1⟩,⟨1,0⟩,⟨1,1⟩] i
      | .inr (e,b) => if b then ⟨2,e⟩ else if e=0 then ⟨0,2⟩ else ⟨1,2⟩
    left_inv := by
      rintro ⟨v,i⟩
      fin_cases v <;> fin_cases i <;> rfl
    right_inv := by
      intro p
      cases p with
      | inl i => fin_cases i <;> rfl
      | inr p =>
        rcases p with ⟨e,b⟩
        fin_cases e <;> cases b <;> rfl }

def side (v : Fin 3) : Bool := decide (v=2)
theorem path_bipartite (e : Fin 2) :
    side (shape.ports.symm (.inr (e,false))).1=false ∧
    side (shape.ports.symm (.inr (e,true))).1=true := by
  fin_cases e <;> exact ⟨rfl,rfl⟩

def network : Network ℤ 4 where
  shape := shape
  vertex v := exactOne (shape.arity v)
  edge := fun _ => Signature.equality

private def ends : ((Fin 2 × Bool) → Bool) ≃ ((Bool × Bool) × (Bool × Bool)) where
  toFun z := ((z (0,false),z (0,true)),(z (1,false),z (1,true)))
  invFun p := fun e => if e.1=0 then if e.2 then p.1.2 else p.1.1
    else if e.2 then p.2.2 else p.2.1
  left_inv := by
    intro z
    funext e
    rcases e with ⟨i,b⟩
    fin_cases i <;> cases b <;> rfl
  right_inv := by
    rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
    rfl

/-- Sum over all independent endpoint bits. Equality on each ordinary
matching edge forces the two ends to agree; no endpoint is deleted for free.
-/
theorem network_sum (t : Word) : network.denote t=
    ∑ a : Bool, ∑ b : Bool,
      exactOne 3 ![t 0,t 1,a]*exactOne 2 ![a,b]*exactOne 3 ![t 2,t 3,b] := by
  have h0 (z : (Fin 2 × Bool) → Bool) :
      shape.assignment t z 0=![t 0,t 1,z (0,false)] := by
    funext i
    fin_cases i <;> rfl
  have h1 (z : (Fin 2 × Bool) → Bool) :
      shape.assignment t z 1=![t 2,t 3,z (1,false)] := by
    funext i
    fin_cases i <;> rfl
  have h2 (z : (Fin 2 × Bool) → Bool) :
      shape.assignment t z 2=![z (0,true),z (1,true)] := by
    funext i
    fin_cases i <;> rfl
  unfold Network.denote
  simp only [network,Fin.prod_univ_three,Fin.prod_univ_two]
  change (∑ z : (Fin 2 × Bool) → Bool,
    exactOne 3 (shape.assignment t z 0)*exactOne 3 (shape.assignment t z 1)*
      exactOne 2 (shape.assignment t z 2)*
      (Signature.equality (z (0,false)) (z (0,true))*
       Signature.equality (z (1,false)) (z (1,true))))=_
  simp_rw [h0,h1,h2]
  rw [← ends.symm.sum_comp]
  simp [ends,Fintype.sum_prod_type,Fintype.sum_bool,Signature.equality] <;> ring

private theorem literal_sum (a b c d : Bool) :
    (∑ u : Bool, ∑ v : Bool,
      exactOne 3 ![a,b,u]*exactOne 2 ![u,v]*exactOne 3 ![c,d,v])=
        exactOne 4 ![a,b,c,d] := by
  simp only [Fintype.sum_bool]
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [exactOne, List.ofFn_succ]

/-- A real bipartite path replacement of the degree-four vertex, with
scalar one and exactly its full four-port matching signature. -/
theorem network_exact (t : Word) : network.denote t=exactOne 4 t := by
  rw [network_sum]
  simpa only [word_eta] using literal_sum (t 0) (t 1) (t 2) (t 3)

def PathLegal (t : Word) (p : Bool × Bool) : Prop :=
  exactOne 3 ![t 0,t 1,p.1]=1 ∧ exactOne 2 ![p.1,p.2]=1 ∧ exactOne 3 ![t 2,t 3,p.2]=1

def canonical (t : Word) : Bool × Bool := (!(t 0 || t 1),!(t 2 || t 3))

private theorem literal_extension (a b c d u v : Bool) :
    PathLegal ![a,b,c,d] (u,v) ↔
      exactOne 4 ![a,b,c,d]=1 ∧ (u,v)=canonical ![a,b,c,d] := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases u <;> cases v <;> norm_num [PathLegal,exactOne,canonical,List.ofFn_succ]

theorem extension_spec (t : Word) (p : Bool × Bool) :
    PathLegal t p ↔ exactOne 4 t=1 ∧ p=canonical t := by
  rcases p with ⟨u,v⟩
  simpa only [word_eta] using literal_extension (t 0) (t 1) (t 2) (t 3) u v

/-- Every supported external word has one actual pair of internal matching
choices, and every unsupported word has none. No multiplicity/scalar arises.
-/
theorem unique_extension (t : Word) :
    (∃! p : Bool × Bool, PathLegal t p) ↔ exactOne 4 t=1 := by
  constructor
  · rintro ⟨p,hp,_⟩
    exact ((extension_spec t p).mp hp).1
  · intro ht
    refine ⟨canonical t,(extension_spec t _).mpr ⟨ht,rfl⟩,?_⟩
    intro p hp
    exact ((extension_spec t p).mp hp).2

theorem no_extension (t : Word) (h : exactOne 4 t=0) : ¬∃ p,PathLegal t p := by
  rintro ⟨p,hp⟩
  have hn := ((extension_spec t p).mp hp).1
  rw [h] at hn
  norm_num at hn

end DegreeFour

end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.ValiantXor
