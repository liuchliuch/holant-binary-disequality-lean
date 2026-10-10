import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Programs
import Holant.Proofs.Counting.VerifierCompiler.Stateful.CapacityFrontend.Unary


noncomputable section
namespace Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Backend
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.Complexity.BinaryInterpolation.WeightCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.CountingHardness.VerifierCompiler.Stateful.CapacityFrontend
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation

def baseRow (m : ℕ) : LocalVertex :=
  (0,if m=0 then [.inl 0,.inl 1,.inl 2]
     else [.inr (0,false),.inl (m+1),.inl (m+2)])
def xRow (k : ℕ) : LocalVertex :=
  (1,[.inr (2*k,true),.inr (2*k+1,false)])
def tRow (m k : ℕ) : LocalVertex :=
  (0,if k+1=m then [.inl 0,.inl 1,.inr (2*k+1,true)]
     else [.inr (2*k+2,false),.inl (m-k),.inr (2*k+1,true)])
def treeRows (m : ℕ) : List LocalVertex :=
  [baseRow m] ++ (List.range m).flatMap (fun k => [xRow k,tRow m k])
def moveRow (m : ℕ) (row : LocalVertex) : LocalVertex :=
  (row.1,row.2.map (Tree.moved m))

private theorem flatMap_congr_on {A B : Type} (xs : List A) (f g : A → List B)
    (h : ∀ a∈xs,f a=g a) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [List.flatMap_cons,List.flatMap_cons,h a (by simp),ih (fun b hb => h b (by simp [hb]))]
theorem move_base (m : ℕ) : moveRow m (baseRow m)=baseRow (m+1) := by
  cases m with
  | zero => rfl
  | succ m => simp [moveRow,baseRow,Tree.moved,Nat.add_assoc]
theorem move_x (m k : ℕ) : moveRow m (xRow k)=xRow k := rfl
theorem move_t (m k : ℕ) (hk : k<m) : moveRow m (tRow m k)=tRow (m+1) k := by
  have hn : k+1≠m+1 := by omega
  by_cases hl : k+1=m
  · have h1 : m+1-k=2 := by omega
    have h2 : 2*k+2=2*m := by omega
    simp [moveRow,tRow,hl,hn,Tree.moved,h1,h2]
  · have h0 : m-k=(m-k-1)+1 := by omega
    have h1 : m+1-k=(m-k-1)+2 := by omega
    simp only [moveRow,tRow,if_neg hl,if_neg hn,List.map_cons,List.map_nil]
    rw [h0,h1]
    simp only [Tree.moved]

/-- Byte-order equality, not a graph isomorphism or a target layout premise. -/
theorem treeRows_exact (m : ℕ) : treeRows m=(Tree.template m).vertices := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have ht : ((List.range m).flatMap (fun k => [xRow k,tRow m k])).map (moveRow m) =
          (List.range m).flatMap (fun k => [xRow k,tRow (m+1) k]) := by
        rw [List.map_flatMap]
        apply flatMap_congr_on
        intro k hk
        simp [move_x,move_t m k (List.mem_range.mp hk)]
      rw [Tree.template,←ih]
      change treeRows (m+1)=(treeRows m).map (moveRow m) ++
        [xRow m,(0,[.inl 0,.inl 1,.inr (2*m+1,true)])]
      simp only [treeRows,List.range_succ,List.flatMap_append,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.map_append,List.map_cons,List.map_nil]
      rw [move_base,ht]
      simp [tRow,List.append_assoc]

def cost (ps : List RawEndpoint) : ℕ := 2*(ps.length-3)
abbrev Args := ℕ × List (List RawEndpoint)
def argsEncoding := pairEncoding unary (framedListEncoding (framedListEncoding RawClosedNetwork.endpointEncoding))
def args (g : UnitInput) : Args := (g.val.2.length,(Compiler.virtual g).vertices.map Prod.snd)
def prefixCost (xs : List (List RawEndpoint)) (j : ℕ) : ℕ := ((xs.take j).map cost).sum
def offset (x : Args) (j : ℕ) : ℕ := x.1+prefixCost x.2 j
def placed (x : Args) (j : ℕ) : List RawVertex :=
  let ps := x.2.getD j []
  (Compiler.degreeTemplate ps.length).placeVertices (offset x j) ps
def vertices (x : Args) : List RawVertex :=
  (List.range x.2.length).flatMap (placed x)
def edgeCount (x : Args) : ℕ := x.1+(x.2.map cost).sum
def raw (x : Args) : RawClosedNetwork := ⟨vertices x,List.replicate (edgeCount x) 0⟩

theorem template_edges (d : ℕ) :
    (Compiler.degreeTemplate d).edges=List.replicate (2*(d-3)) 0 := by
  rcases d with _ | _ | _ | m
  · rfl
  · rfl
  · rfl
  · have ht : ∀ k,(Tree.template k).edges=List.replicate (2*k) 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
          have he : 2*(k+1)=2*k+2 := by omega
          simp [Tree.template,ih,he,List.replicate_add,-List.replicate_append_replicate]
    simpa [Compiler.degreeTemplate] using ht m
theorem cost_exact (ps : List RawEndpoint) :
    cost ps=(Compiler.degreeTemplate ps.length).edges.length := by
  rw [template_edges]
  simp [cost]
theorem prefix_cons (ps : List RawEndpoint) (xs : List (List RawEndpoint)) (j : ℕ) :
    prefixCost (ps::xs) (j+1)=cost ps+prefixCost xs j := by
  simp [prefixCost]
theorem placed_cons (off : ℕ) (ps : List RawEndpoint) (xs : List (List RawEndpoint)) (j : ℕ) :
    placed (off,ps::xs) (j+1)=placed (off+cost ps,xs) j := by
  simp [placed,offset,prefix_cons,Nat.add_assoc]
theorem vertices_expand (off : ℕ) (xs : List (List RawEndpoint)) :
    vertices (off,xs)=
      (expandRows Compiler.degreeTemplate off (xs.map (fun ps => (ps.length,ps)))).vertices := by
  induction xs generalizing off with
  | nil => rfl
  | cons ps xs ih =>
      simp only [vertices,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
        List.flatMap_map,List.map_cons,expandRows]
      have htail : (fun i => placed (off,ps::xs) (i+1))=placed (off+cost ps,xs) := by
        funext i
        exact placed_cons off ps xs i
      rw [htail]
      change placed (off,ps::xs) 0 ++ vertices (off+cost ps,xs)=_
      rw [ih,cost_exact]
      rfl
theorem edges_expand (off : ℕ) (xs : List (List RawEndpoint)) :
    (expandRows Compiler.degreeTemplate off (xs.map (fun ps => (ps.length,ps)))).edges=
      List.replicate (xs.map cost).sum 0 := by
  induction xs generalizing off with
  | nil => rfl
  | cons ps xs ih =>
      simp only [List.map_cons,expandRows,List.sum_cons]
      rw [ih,template_edges]
      simp [cost,List.replicate_add,-List.replicate_append_replicate]
theorem raw_replace (x : Args) : raw x=replace Compiler.degreeTemplate
    ⟨x.2.map (fun ps => (ps.length,ps)),List.replicate x.1 0⟩ := by
  rcases x with ⟨off,xs⟩
  unfold raw replace
  rw [vertices_expand]
  simp only [List.length_replicate]
  rw [edges_expand]
  simp [edgeCount,List.replicate_add,-List.replicate_append_replicate]

/-- The target graph is exactly the previously delivered Compiler.queryRaw. -/
theorem raw_unit (g : UnitInput) : raw (args g)=Compiler.queryRaw g := by
  rw [raw_replace]
  unfold args Compiler.queryRaw
  congr 1
  simp [Compiler.virtual,List.map_map,Function.comp_def]

/-- Bounds are generated from the original UnitValid occurrence table. They
are not row-loop limits or caller budgets added to the input protocol. -/
theorem table_length (g : UnitInput) : (args g).2.length=2*g.val.1 := by
  simp [args,Compiler.virtual,Compiler.nodes]
  omega
theorem degree_bound (g : UnitInput) (j : ℕ) (hj : j<(args g).2.length) :
    ((args g).2.getD j []).length≤g.val.2.length := by
  have hm : (args g).2.getD j []∈(args g).2 := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨row,hr,he⟩ := List.mem_map.mp hm
  obtain ⟨p,hp,hr'⟩ := List.mem_map.mp hr
  rw [←he,←hr']
  exact Compiler.ports_bound g p.1 p.2
theorem degree_input_bound (g : UnitInput) (j : ℕ) (hj : j<(args g).2.length) :
    ((args g).2.getD j []).length≤(unitEncoding.encode g).length ∧
    (((args g).2.getD j []).length-3)≤(unitEncoding.encode g).length := by
  have h := (degree_bound g j hj).trans (unit_input_counts g).2
  exact ⟨h,(Nat.sub_le _ _).trans h⟩

namespace Code
abbrev portEncoding := framedListEncoding RawClosedNetwork.endpointEncoding
abbrev tableEncoding := framedListEncoding portEncoding
abbrev Row := Args × ℕ
def rowEncoding := pairEncoding argsEncoding unary
abbrev Cell := Row × ℕ
def cellEncoding := pairEncoding rowEncoding unary

variable {A : Type} {ea : Encoding A Bool}
def add {f g : A → ℕ} (u : Computes ea unary f) (v : Computes ea unary g) :
    Computes ea unary (fun a => f a+g a) := (pairComputes u v).andThen Unary.addComputes
def sub {f g : A → ℕ} (u : Computes ea unary f) (v : Computes ea unary g) :
    Computes ea unary (fun a => f a-g a) := (pairComputes u v).andThen Unary.subtractComputes
def eq {f g : A → ℕ} (u : Computes ea unary f) (v : Computes ea unary g) :
    Computes ea encodingBoolBool (fun a => decide (f a=g a)) :=
  (pairComputes u v).andThen (equalComputes unary)
def nat (e : Encoding A Bool) (n : ℕ) : Computes e unary (fun _ => n) := constantComputes e unary n
def bool (e : Encoding A Bool) (b : Bool) : Computes e encodingBoolBool (fun _ => b) :=
  constantComputes e encodingBoolBool b
def endpoint {f : A → ℕ} {b : A → Bool} (u : Computes ea unary f) (v : Computes ea encodingBoolBool b) :
    Computes ea RawClosedNetwork.endpointEncoding (fun a => (f a,b a)) :=
  recode (pairComputes (u.andThen UnaryBinary.computes) v) id (fun _ => rfl) (fun _ => rfl)
def row1 {f : A → RawEndpoint} (tag : ℕ) (u : Computes ea RawClosedNetwork.endpointEncoding f) :
    Computes ea RawClosedNetwork.vertexEncoding (fun a => (tag,[f a])) := by
  let w : Computes ea portEncoding (fun a => [f a]) :=
    fixedListComputes ea RawClosedNetwork.endpointEncoding (fun a (_ : Fin 1) => f a)
      (fun _ => u) [0]
  exact recode (pairComputes (constantComputes ea encodingNatBool tag) w)
    id (fun _ => rfl) (fun _ => rfl)
def row2 {f g : A → RawEndpoint} (tag : ℕ)
    (u : Computes ea RawClosedNetwork.endpointEncoding f)
    (v : Computes ea RawClosedNetwork.endpointEncoding g) :
    Computes ea RawClosedNetwork.vertexEncoding (fun a => (tag,[f a,g a])) := by
  let F (a : A) (i : Fin 2) := if i=0 then f a else g a
  let providers : (i : Fin 2) → Computes ea RawClosedNetwork.endpointEncoding (fun a => F a i) :=
    Fin.cases (by simpa [F] using u) (fun i =>
      Fin.cases (by simpa [F] using v) (fun j => Fin.elim0 j) i)
  let w := fixedListComputes ea RawClosedNetwork.endpointEncoding F providers [0,1]
  exact recode (pairComputes (constantComputes ea encodingNatBool tag) w)
    id (fun _ => rfl) (fun _ => rfl)
def row3 {f g h : A → RawEndpoint} (tag : ℕ)
    (u : Computes ea RawClosedNetwork.endpointEncoding f)
    (v : Computes ea RawClosedNetwork.endpointEncoding g)
    (w : Computes ea RawClosedNetwork.endpointEncoding h) :
    Computes ea RawClosedNetwork.vertexEncoding (fun a => (tag,[f a,g a,h a])) := by
  let F (a : A) (i : Fin 3) := if i=0 then f a else if i=1 then g a else h a
  let providers : (i : Fin 3) → Computes ea RawClosedNetwork.endpointEncoding (fun a => F a i) :=
    Fin.cases (by simpa [F] using u) (fun i =>
      Fin.cases (by simpa [F] using v) (fun j =>
        Fin.cases (by simpa [F] using w) (fun k => Fin.elim0 k) j) i)
  let ports := fixedListComputes ea RawClosedNetwork.endpointEncoding F providers [0,1,2]
  exact recode (pairComputes (constantComputes ea encodingNatBool tag) ports)
    id (fun _ => rfl) (fun _ => rfl)

def arrays : Computes argsEncoding tableEncoding (fun x : Args => x.2) := Wiring.secondComputes _ _
def oldEdges : Computes argsEncoding unary (fun x : Args => x.1) := Wiring.firstComputes _ _
def rowContext : Computes rowEncoding argsEncoding (fun x : Row => x.1) := Wiring.firstComputes _ _
def rowIndex : Computes rowEncoding unary (fun x : Row => x.2) := Wiring.secondComputes _ _
def ports : Computes rowEncoding portEncoding (fun x : Row => x.1.2.getD x.2 []) :=
  (pairComputes (rowContext.andThen arrays) rowIndex).andThen (WireLists.getD portEncoding [])
def degree : Computes rowEncoding unary (fun x : Row => (x.1.2.getD x.2 []).length) :=
  ports.andThen (WireLists.lengthComputes RawClosedNetwork.endpointEncoding)
def depth : Computes rowEncoding unary (fun x : Row => (x.1.2.getD x.2 []).length-3) :=
  sub degree (nat rowEncoding 3)
def internalCount : Computes rowEncoding unary (fun x : Row => cost (x.1.2.getD x.2 [])) :=
  depth.andThen (Unary.scaleComputes 2)

private theorem prefix_word (xs : List (List RawEndpoint)) (j : ℕ) :
    (List.range j).flatMap (fun i => List.replicate (cost (xs.getD i [])) true)=
      List.replicate (prefixCost xs j) true := by
  induction xs generalizing j with
  | nil => simp [prefixCost,cost]
  | cons ps xs ih =>
      cases j with
      | zero => rfl
      | succ j =>
          simp only [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
          simp only [List.getD_cons_zero,List.getD_cons_succ]
          rw [ih]
          simp [prefixCost,List.replicate_add,-List.replicate_append_replicate]

def «prefix» : Computes rowEncoding unary (fun x : Row => prefixCost x.1.2 x.2) := by
  let ec := pairEncoding rowEncoding unary
  let old := Wiring.firstComputes rowEncoding unary
  let index := Wiring.secondComputes rowEncoding unary
  let prepare : Computes ec rowEncoding (fun x : Row × ℕ => (x.1.1,x.2)) :=
    pairComputes (old.andThen rowContext) index
  let piece := (prepare.andThen internalCount).andThen (encodeComputes unary)
  let words := rangeWordsComputes rowEncoding Prod.snd rowIndex
    (fun x : Row × ℕ => unary.encode (cost (x.1.1.2.getD x.2 []))) piece
  exact recode words id (fun _ => rfl) (fun x => by
    simpa only [Frame.wordEncoding,unary,UnaryBinary.unaryEncoding,id_eq] using prefix_word x.1.2 x.2)
def offset : Computes rowEncoding unary (fun x : Row => Backend.offset x.1 x.2) :=
  add (rowContext.andThen oldEdges) «prefix»
def boundary {f : Row → ℕ} (i : Computes rowEncoding unary f) :
    Computes rowEncoding RawClosedNetwork.endpointEncoding
      (fun x : Row => (x.1.2.getD x.2 []).getD (f x) (0,false)) :=
  (pairComputes ports i).andThen (WireLists.getD RawClosedNetwork.endpointEncoding (0,false))
def internal {f : Row → ℕ} (i : Computes rowEncoding unary f) (b : Bool) :
    Computes rowEncoding RawClosedNetwork.endpointEncoding
      (fun x : Row => (Backend.offset x.1 x.2+f x,b)) :=
  endpoint (add offset i) (bool rowEncoding b)

def base : Computes rowEncoding RawClosedNetwork.vertexEncoding
    (fun x : Row =>
      let ps := x.1.2.getD x.2 []
      let m := ps.length-3
      ((baseRow m).1,(baseRow m).2.map (Template.placeEndpoint (Backend.offset x.1 x.2) ps))) := by
  let test := eq depth (nat rowEncoding 0)
  let a := ifComputes test (boundary (nat rowEncoding 0)) (internal (nat rowEncoding 0) false)
  let b := ifComputes test (boundary (nat rowEncoding 1)) (boundary (add depth (nat rowEncoding 1)))
  let c := ifComputes test (boundary (nat rowEncoding 2)) (boundary (add depth (nat rowEncoding 2)))
  exact congrComputes (row3 0 a b c) (fun x => by
    unfold baseRow
    split_ifs <;> simp_all [Template.placeEndpoint,Nat.add_zero])

def cellContext : Computes cellEncoding rowEncoding (fun x : Cell => x.1) := Wiring.firstComputes _ _
def cellIndex : Computes cellEncoding unary (fun x : Cell => x.2) := Wiring.secondComputes _ _
def cellBoundary {f : Cell → ℕ} (i : Computes cellEncoding unary f) :
    Computes cellEncoding RawClosedNetwork.endpointEncoding
      (fun x : Cell => (x.1.1.2.getD x.1.2 []).getD (f x) (0,false)) :=
  (pairComputes (cellContext.andThen ports) i).andThen (WireLists.getD RawClosedNetwork.endpointEncoding (0,false))
def cellInternal {f : Cell → ℕ} (i : Computes cellEncoding unary f) (b : Bool) :
    Computes cellEncoding RawClosedNetwork.endpointEncoding
      (fun x : Cell => (Backend.offset x.1.1 x.1.2+f x,b)) :=
  endpoint (add (cellContext.andThen offset) i) (bool cellEncoding b)
def xCell : Computes cellEncoding RawClosedNetwork.vertexEncoding
    (fun x : Cell =>
      let ps := x.1.1.2.getD x.1.2 []
      ((xRow x.2).1,(xRow x.2).2.map (Template.placeEndpoint (Backend.offset x.1.1 x.1.2) ps))) :=
  congrComputes (row2 1 (cellInternal (add cellIndex cellIndex) true)
    (cellInternal (add (add cellIndex cellIndex) (nat cellEncoding 1)) false))
    (fun _ => by simp [xRow,Template.placeEndpoint,two_mul])
def tCell : Computes cellEncoding RawClosedNetwork.vertexEncoding
    (fun x : Cell =>
      let ps := x.1.1.2.getD x.1.2 []
      ((tRow (ps.length-3) x.2).1,
       (tRow (ps.length-3) x.2).2.map (Template.placeEndpoint (Backend.offset x.1.1 x.1.2) ps))) := by
  let test := eq (add cellIndex (nat cellEncoding 1)) (cellContext.andThen depth)
  let a := ifComputes test (cellBoundary (nat cellEncoding 0))
    (cellInternal (add (add cellIndex cellIndex) (nat cellEncoding 2)) false)
  let b := ifComputes test (cellBoundary (nat cellEncoding 1))
    (cellBoundary (sub (cellContext.andThen depth) cellIndex))
  let c := cellInternal (add (add cellIndex cellIndex) (nat cellEncoding 1)) true
  exact congrComputes (row3 0 a b c) (fun x => by
    unfold tRow
    split_ifs <;> simp_all [Template.placeEndpoint,two_mul])
def cellBytes : Computes cellEncoding Frame.wordEncoding
    (fun x : Cell =>
      let ps := x.1.1.2.getD x.1.2 []
      entries RawClosedNetwork.vertexEncoding
        ([xRow x.2,tRow (ps.length-3) x.2].map
          (fun row => (row.1,row.2.map (Template.placeEndpoint (Backend.offset x.1.1 x.1.2) ps))))) :=
  congrComputes (joinComputes (xCell.andThen (entryComputes RawClosedNetwork.vertexEncoding))
    (tCell.andThen (entryComputes RawClosedNetwork.vertexEncoding)))
    (fun _ => by simp [entries])

def highBytes : Computes rowEncoding Frame.wordEncoding
    (fun x : Row =>
      let ps := x.1.2.getD x.2 []
      entries RawClosedNetwork.vertexEncoding
        ((treeRows (ps.length-3)).map
          (fun row => (row.1,row.2.map (Template.placeEndpoint (Backend.offset x.1 x.2) ps))))) := by
  let chain := rangeWordsComputes rowEncoding (fun x : Row => (x.1.2.getD x.2 []).length-3)
    depth _ cellBytes
  exact congrComputes (joinComputes (base.andThen (entryComputes RawClosedNetwork.vertexEncoding)) chain)
    (fun x => by simp [treeRows,entries,List.flatMap_assoc,List.map_flatMap,List.flatMap_map])

def placedBytes : Computes rowEncoding Frame.wordEncoding
    (fun x : Row => entries RawClosedNetwork.vertexEncoding (placed x.1 x.2)) := by
  let empty := constantComputes rowEncoding Frame.wordEncoding []
  let pin := (row1 2 (boundary (nat rowEncoding 0))).andThen (entryComputes RawClosedNetwork.vertexEncoding)
  let x := (row2 1 (boundary (nat rowEncoding 0)) (boundary (nat rowEncoding 1))).andThen
    (entryComputes RawClosedNetwork.vertexEncoding)
  let code := ifComputes (eq degree (nat rowEncoding 0)) empty
    (ifComputes (eq degree (nat rowEncoding 1)) pin
      (ifComputes (eq degree (nat rowEncoding 2)) x highBytes))
  exact congrComputes code (fun a => by
    generalize hd : (a.1.2.getD a.2 []).length=d
    simp only [List.getD] at hd
    rcases d with _ | _ | _ | m
    · simp [placed,Compiler.degreeTemplate,Template.placeVertices,hd,entries]
    · simp [placed,Compiler.degreeTemplate,Template.placeVertices,hd,entries,Template.placeEndpoint]
    · simp [placed,Compiler.degreeTemplate,Template.placeVertices,hd,entries,Template.placeEndpoint]
    · simp [placed,Compiler.degreeTemplate,Template.placeVertices,hd,←treeRows_exact,entries])

def vertexBytes : Computes argsEncoding Frame.wordEncoding
    (fun x : Args => entries RawClosedNetwork.vertexEncoding (Backend.vertices x)) :=
  congrComputes (rangeWordsComputes argsEncoding (fun x : Args => x.2.length)
    (arrays.andThen (WireLists.lengthComputes portEncoding)) _ placedBytes)
    (fun _ => by simp [Backend.vertices,entries,List.flatMap_assoc])
def vertexList : Computes argsEncoding (framedListEncoding RawClosedNetwork.vertexEncoding) Backend.vertices :=
  recode (joinComputes vertexBytes (constantComputes argsEncoding Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun x => by
      simpa only [Frame.wordEncoding,framedListEncoding,framedListEncode,List.append_nil,id_eq] using
        entries_append_encode RawClosedNetwork.vertexEncoding (Backend.vertices x) [])
def count : Computes argsEncoding unary Backend.edgeCount :=
  congrComputes ((pairComputes (identityComputes argsEncoding)
    (arrays.andThen (WireLists.lengthComputes portEncoding))).andThen offset)
    (fun x => by
      have ht : (x.2.map cost).take x.2.length=x.2.map cost := List.take_of_length_le (by simp)
      simp [Backend.offset,prefixCost,Backend.edgeCount,ht])
def edgeList : Computes argsEncoding (framedListEncoding encodingNatBool)
    (fun x : Args => List.replicate (Backend.edgeCount x) 0) :=
  count.andThen (WireLists.replicate encodingNatBool 0)
def rawComputes : Computes argsEncoding RawClosedNetwork.encoding Backend.raw :=
  recode (pairComputes vertexList edgeList) id (fun _ => rfl) (fun _ => rfl)

def rawPorts : Computes RawClosedNetwork.encoding tableEncoding
    (fun r : RawClosedNetwork => r.vertices.map Prod.snd) :=
  recode ((Wiring.firstComputes (framedListEncoding RawClosedNetwork.vertexEncoding)
    (framedListEncoding encodingNatBool)).andThen
      (WireLists.mapComputes RawClosedNetwork.vertexEncoding portEncoding Prod.snd
        (recode (Wiring.secondComputes encodingNatBool portEncoding) id (fun _ => rfl) (fun _ => rfl))))
    (fun r => (r.vertices,r.edges)) (fun _ => rfl) (fun _ => rfl)
def rawCount : Computes RawClosedNetwork.encoding unary (fun r : RawClosedNetwork => r.edges.length) :=
  recode ((Wiring.secondComputes (framedListEncoding RawClosedNetwork.vertexEncoding)
    (framedListEncoding encodingNatBool)).andThen (WireLists.lengthComputes encodingNatBool))
    (fun r => (r.vertices,r.edges)) (fun _ => rfl) (fun _ => rfl)
def prepare : Computes unitEncoding argsEncoding Backend.args :=
  congrComputes (Programs.virtualComputes.andThen (pairComputes rawCount rawPorts))
    (fun g => by simp [Backend.args,Compiler.virtual])

/-- Uniform original-bit -> final SAME validated fixed-alphabet query. -/
def computes : Computes unitEncoding (RawClosedNetwork.validatedEncoding 3 1 Tree.arity) Compiler.query :=
  recode (congrComputes (prepare.andThen rawComputes) raw_unit)
    id (fun _ => rfl) (fun _ => rfl)
theorem query_execution (g : UnitInput) : Programs.RunsExactly computes.machine.computer.step
    (initList computes.machine.computer (unitEncoding.encode g))
    (haltList computes.machine.computer (Compiler.queryBits g)) (computes.outputs g).steps :=
  (computes.outputs g).evals_in_steps
theorem query_time (g : UnitInput) :
    (computes.outputs g).steps≤computes.time.eval (unitEncoding.encode g).length :=
  (computes.outputs g).steps_le_m
theorem query_primitive (g : UnitInput) : primitiveCost computes.machine (computes.outputs g).steps
    (some (initList computes.machine.computer (unitEncoding.encode g)))≤
      (primitivePolynomial computes).eval (unitEncoding.encode g).length := computes_primitive_cost computes g
theorem query_storage (g : UnitInput) (t : ℕ) (c : computes.machine.Config)
    (ht : t≤computes.time.eval (unitEncoding.encode g).length)
    (hr : Programs.RunsExactly computes.machine.computer.step (initList computes.machine.computer (unitEncoding.encode g)) c t) :
    stackSize c.stk≤computes.outputBound.bound.eval (unitEncoding.encode g).length := by
  have h := computes.machine.run_size_le _ _ _ hr
  rw [Machine.size_init] at h
  exact h.trans (by
    simpa only [Computes.outputBound,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left (Nat.mul_le_mul_right computes.machine.primitiveBudget ht) (unitEncoding.encode g).length)

end Code

end Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Backend
