import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Programs
import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Backend


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.CountingHardness.VerifierCompiler.Stateful.CapacityFrontend
open WeightedMatchingInterpolation
open Holant.Complexity.BinaryInterpolation.WeightCompiler (rangeWordsComputes)
namespace Renderer
namespace OldCode
export Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Backend.Code
  (add sub eq nat bool endpoint row3)
end OldCode

def baseRow (side : Bool) (m : ℕ) : LocalVertex :=
  (Layout.tag side,if m=0 then [.inl 0,.inl 1,.inl 2]
    else [.inr (0,false),.inl (m+1),.inl (m+2)])
def chainRow (side : Bool) (m k : ℕ) : LocalVertex :=
  (Layout.tag side,if k+1=m then [.inl 0,.inl 1,.inr (k,true)]
    else [.inr (k+1,false),.inl (m-k),.inr (k,true)])
def treeRows (side : Bool) (m : ℕ) : List LocalVertex :=
  [baseRow side m]++(List.range m).map (chainRow side m)
def moveRow (m : ℕ) (r : LocalVertex) : LocalVertex := (r.1,r.2.map (Layout.moved m))
theorem move_base (side : Bool) (m : ℕ) : moveRow m (baseRow side m)=baseRow side (m+1) := by
  cases m <;> simp [moveRow,baseRow,Layout.moved,Nat.add_assoc]
theorem move_chain (side : Bool) (m k : ℕ) (hk : k<m) :
    moveRow m (chainRow side m k)=chainRow side (m+1) k := by
  have hn : k+1≠m+1 := by omega
  by_cases hl : k+1=m
  · have h1 : m+1-k=2 := by omega
    have h2 : k+1=m := hl
    simp [moveRow,chainRow,hl,hn,Layout.moved,h1,h2]
  · have h0 : m-k=(m-k-1)+1 := by omega
    have h1 : m+1-k=(m-k-1)+2 := by omega
    simp only [moveRow,chainRow,if_neg hl,if_neg hn,List.map_cons,List.map_nil]
    rw [h0,h1]
    rfl
theorem treeRows_exact (side : Bool) (m : ℕ) : treeRows side m=(Layout.tree side m).vertices := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have ht : ((List.range m).map (chainRow side m)).map (moveRow m)=
          (List.range m).map (chainRow side (m+1)) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro k hk
        exact move_chain side m k (List.mem_range.mp hk)
      rw [Layout.tree,←ih]
      change treeRows side (m+1)=(treeRows side m).map (moveRow m)++
        [(Layout.tag side,[.inl 0,.inl 1,.inr (m,true)])]
      simp only [treeRows,List.range_succ,List.map_append,List.map_cons,List.map_nil]
      rw [move_base,ht]
      simp [chainRow,List.append_assoc]

abbrev Entry := Bool × List RawEndpoint
abbrev Args := ℕ × List Entry
abbrev Row := Args × ℕ
abbrev Cell := Row × ℕ
abbrev portEncoding := framedListEncoding RawClosedNetwork.endpointEncoding
abbrev entryEncoding := pairEncoding encodingBoolBool portEncoding
abbrev tableEncoding := framedListEncoding entryEncoding
def argsEncoding := pairEncoding UnaryBinary.unaryEncoding tableEncoding
def rowEncoding := pairEncoding argsEncoding UnaryBinary.unaryEncoding
def cellEncoding := pairEncoding rowEncoding UnaryBinary.unaryEncoding
def cost (r : Entry) : ℕ := (r.2.length-3)+2*(3-r.2.length)
def prefixCost (xs : List Entry) (j : ℕ) : ℕ :=
  ((List.range j).map (fun i => cost (xs.getD i (false,[])))).sum
def offset (x : Args) (j : ℕ) : ℕ := x.1+prefixCost x.2 j
def placed (x : Args) (j : ℕ) : List RawVertex :=
  let r := x.2.getD j (false,[])
  (Layout.degree r.1 r.2.length).placeVertices (offset x j) r.2
def vertices (x : Args) : List RawVertex := (List.range x.2.length).flatMap (placed x)
def edgeCount (x : Args) : ℕ := x.1+(x.2.map cost).sum
def raw (x : Args) : RawClosedNetwork := ⟨vertices x,List.replicate (edgeCount x) 0⟩
def args (g : UnitInput) : Args :=
  (g.val.2.length,(OldCompiler.nodes g).map (fun p => (p.1,OldCompiler.ports g p.1 p.2)))
theorem cost_exact (r : Entry) : cost r=(Layout.degree r.1 r.2.length).edges.length :=
  (Layout.degree_counts _ _).2.symm
theorem degree_edges (side : Bool) (d : ℕ) :
    (Layout.degree side d).edges=List.replicate ((d-3)+2*(3-d)) 0 := by
  have ht : ∀ m,(Layout.tree side m).edges=List.replicate m 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        simp only [Layout.tree,ih]
        change List.replicate m 0++List.replicate 1 0=List.replicate (m+1) 0
        exact (List.replicate_add m 1 0).symm
  by_cases h : d≤3
  · simp [Layout.degree,h,Layout.low,show d-3=0 by omega]
  · simp [Layout.degree,h,ht,show 3-d=0 by omega]
theorem prefix_cons (r : Entry) (rs : List Entry) (j : ℕ) :
    prefixCost (r::rs) (j+1)=cost r+prefixCost rs j := by
  simp [prefixCost,List.range_succ_eq_map,List.map_map,Function.comp_def]
theorem prefix_length (rs : List Entry) : prefixCost rs rs.length=(rs.map cost).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [prefix_cons,ih]
theorem vertices_expand (off : ℕ) (rs : List Entry) :
    vertices (off,rs)=
      (expandRows Layout.templates off
        (rs.map (fun r => (2*r.2.length+Layout.tag r.1,r.2)))).vertices := by
  induction rs generalizing off with
  | nil => rfl
  | cons r rs ih =>
      have hlabel : Layout.templates (2*r.2.length+Layout.tag r.1)=Layout.degree r.1 r.2.length := by
        have hd : (2*r.2.length+Layout.tag r.1)/2=r.2.length := by
          have ht := Layout.tag_bound r.1
          omega
        have hs : ((2*r.2.length+Layout.tag r.1)%2==1)=r.1 := by
          cases r.1 <;> simp [Layout.tag]
        unfold Layout.templates
        rw [hd,hs]
      have htail : (fun i => placed (off,r::rs) (i+1))=placed (off+cost r,rs) := by
        funext i
        simp [placed,offset,prefix_cons,Nat.add_assoc]
      simp only [vertices,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
        List.flatMap_map,List.map_cons,expandRows,hlabel]
      rw [htail]
      change placed (off,r::rs) 0++vertices (off+cost r,rs)=_
      rw [ih,cost_exact]
      rfl
theorem edges_expand (off : ℕ) (rs : List Entry) :
    (expandRows Layout.templates off
      (rs.map (fun r => (2*r.2.length+Layout.tag r.1,r.2)))).edges=
        List.replicate (rs.map cost).sum 0 := by
  induction rs generalizing off with
  | nil => rfl
  | cons r rs ih =>
      have hlabel : Layout.templates (2*r.2.length+Layout.tag r.1)=Layout.degree r.1 r.2.length := by
        have hd : (2*r.2.length+Layout.tag r.1)/2=r.2.length := by
          have ht := Layout.tag_bound r.1
          omega
        have hs : ((2*r.2.length+Layout.tag r.1)%2==1)=r.1 := by
          cases r.1 <;> simp [Layout.tag]
        unfold Layout.templates
        rw [hd,hs]
      simp only [List.map_cons,expandRows,hlabel,List.sum_cons]
      rw [ih,degree_edges]
      simp [cost,List.replicate_add,-List.replicate_append_replicate]
theorem raw_unit (g : UnitInput) : raw (args g)=Layout.raw g := by
  have hr : (args g).2.map (fun r => (2*r.2.length+Layout.tag r.1,r.2))=(Layout.virtual g).vertices := by
    simp [args,Layout.virtual,List.map_map,Function.comp_def]
  have hvirt : Layout.virtual g=
      ⟨(args g).2.map (fun r => (2*r.2.length+Layout.tag r.1,r.2)),List.replicate (args g).1 0⟩ :=
    congrArg (fun vs => RawClosedNetwork.mk vs (List.replicate g.val.2.length 0)) hr.symm
  unfold Layout.raw
  rw [hvirt]
  unfold raw replace
  simp only [List.length_replicate]
  rw [vertices_expand,edges_expand]
  simp only [edgeCount,List.replicate_add]

namespace Code
open OldCode
abbrev unary := UnaryBinary.unaryEncoding
def arrays : Computes argsEncoding tableEncoding (fun x : Args => x.2) := Wiring.secondComputes _ _
def oldEdges : Computes argsEncoding unary (fun x : Args => x.1) := Wiring.firstComputes _ _
def context : Computes rowEncoding argsEncoding (fun x : Row => x.1) := Wiring.firstComputes _ _
def index : Computes rowEncoding unary (fun x : Row => x.2) := Wiring.secondComputes _ _
def saved : Computes rowEncoding entryEncoding (fun x : Row => x.1.2.getD x.2 (false,[])) :=
  (pairComputes (context.andThen arrays) index).andThen (WireLists.getD entryEncoding (false,[]))
def side : Computes rowEncoding encodingBoolBool (fun x : Row => (x.1.2.getD x.2 (false,[])).1) :=
  saved.andThen (Wiring.firstComputes encodingBoolBool portEncoding)
def ports : Computes rowEncoding portEncoding (fun x : Row => (x.1.2.getD x.2 (false,[])).2) :=
  saved.andThen (Wiring.secondComputes encodingBoolBool portEncoding)
def degree := ports.andThen (WireLists.lengthComputes RawClosedNetwork.endpointEncoding)
def depth := sub degree (nat rowEncoding 3)
def internalCount : Computes rowEncoding unary (fun x : Row => cost (x.1.2.getD x.2 (false,[]))) :=
  add depth ((sub (nat rowEncoding 3) degree).andThen (Unary.scaleComputes 2))
private theorem prefix_word (xs : List Entry) (j : ℕ) :
    (List.range j).flatMap (fun i => List.replicate (cost (xs.getD i (false,[]))) true)=
      List.replicate (prefixCost xs j) true := by
  unfold prefixCost
  induction List.range j with
  | nil => rfl
  | cons i is ih =>
      simp only [List.flatMap_cons,List.map_cons,List.sum_cons,List.replicate_add,ih]
def «prefix» : Computes rowEncoding unary (fun x : Row => prefixCost x.1.2 x.2) := by
  let outer := Wiring.firstComputes rowEncoding unary
  let inner := Wiring.secondComputes rowEncoding unary
  let prepare : Computes (pairEncoding rowEncoding unary) rowEncoding
      (fun x : Row × ℕ => (x.1.1,x.2)) := pairComputes (outer.andThen context) inner
  let piece := (prepare.andThen internalCount).andThen (encodeComputes unary)
  let words := rangeWordsComputes rowEncoding Prod.snd index _ piece
  exact recode words id (fun _ => rfl) (fun x => by
    simpa only [Frame.wordEncoding,unary,UnaryBinary.unaryEncoding,id_eq,Function.comp_def] using prefix_word x.1.2 x.2)
def offset : Computes rowEncoding unary (fun x : Row => Renderer.offset x.1 x.2) :=
  add (context.andThen oldEdges) «prefix»
def placement : Computes rowEncoding placementEncoding
    (fun x : Row => (Renderer.offset x.1 x.2,(x.1.2.getD x.2 (false,[])).2)) :=
  pairComputes (offset.andThen UnaryBinary.computes) ports
def boundary {f : Row → ℕ} (i : Computes rowEncoding unary f) :=
  (pairComputes ports i).andThen (WireLists.getD RawClosedNetwork.endpointEncoding (0,false))
def internal {f : Row → ℕ} (i : Computes rowEncoding unary f) (b : Bool) :=
  endpoint (add offset i) (bool rowEncoding b)
def base (s : Bool) : Computes rowEncoding RawClosedNetwork.vertexEncoding
    (fun x : Row =>
      let ps := (x.1.2.getD x.2 (false,[])).2
      ((baseRow s (ps.length-3)).1,
        (baseRow s (ps.length-3)).2.map (Template.placeEndpoint (Renderer.offset x.1 x.2) ps))) := by
  let test := eq depth (nat rowEncoding 0)
  let a := ifComputes test (boundary (nat rowEncoding 0)) (internal (nat rowEncoding 0) false)
  let b := ifComputes test (boundary (nat rowEncoding 1)) (boundary (add depth (nat rowEncoding 1)))
  let c := ifComputes test (boundary (nat rowEncoding 2)) (boundary (add depth (nat rowEncoding 2)))
  exact congrComputes (row3 (Layout.tag s) a b c) (fun x => by
    unfold baseRow
    split_ifs <;> simp_all [Template.placeEndpoint,Nat.add_zero])
def cellContext : Computes cellEncoding rowEncoding (fun x : Cell => x.1) := Wiring.firstComputes _ _
def cellIndex : Computes cellEncoding unary (fun x : Cell => x.2) := Wiring.secondComputes _ _
def cellBoundary {f : Cell → ℕ} (i : Computes cellEncoding unary f) :=
  (pairComputes (cellContext.andThen ports) i).andThen
    (WireLists.getD RawClosedNetwork.endpointEncoding (0,false))
def cellInternal {f : Cell → ℕ} (i : Computes cellEncoding unary f) (b : Bool) :=
  endpoint (add (cellContext.andThen offset) i) (bool cellEncoding b)
def chain (s : Bool) : Computes cellEncoding RawClosedNetwork.vertexEncoding
    (fun x : Cell =>
      let ps := (x.1.1.2.getD x.1.2 (false,[])).2
      ((chainRow s (ps.length-3) x.2).1,
        (chainRow s (ps.length-3) x.2).2.map (Template.placeEndpoint (Renderer.offset x.1.1 x.1.2) ps))) := by
  let test := eq (add cellIndex (nat cellEncoding 1)) (cellContext.andThen depth)
  let a := ifComputes test (cellBoundary (nat cellEncoding 0))
    (cellInternal (add cellIndex (nat cellEncoding 1)) false)
  let b := ifComputes test (cellBoundary (nat cellEncoding 1))
    (cellBoundary (sub (cellContext.andThen depth) cellIndex))
  exact congrComputes (row3 (Layout.tag s) a b (cellInternal cellIndex true))
    (fun x => by unfold chainRow; split_ifs <;> simp_all [Template.placeEndpoint])
def high (s : Bool) : Computes rowEncoding Frame.wordEncoding
    (fun x : Row => FixedGadgetSubstitution.Compiler.entries RawClosedNetwork.vertexEncoding
      ((Layout.tree s ((x.1.2.getD x.2 (false,[])).2.length-3)).placeVertices
        (Renderer.offset x.1 x.2) (x.1.2.getD x.2 (false,[])).2)) :=
  congrComputes (joinComputes ((base s).andThen (entryComputes RawClosedNetwork.vertexEncoding))
    (rangeWordsComputes rowEncoding _ depth _
      ((chain s).andThen (entryComputes RawClosedNetwork.vertexEncoding))))
    (fun x => by simp [Template.placeVertices,←treeRows_exact,treeRows,FixedGadgetSubstitution.Compiler.entries,List.map_append,List.flatMap_map])
def low (s : Bool) (d : ℕ) := placement.andThen (templateEntriesComputes (Layout.low s d))
def fixedSide (s : Bool) : Computes rowEncoding Frame.wordEncoding
    (fun x : Row => FixedGadgetSubstitution.Compiler.entries RawClosedNetwork.vertexEncoding
      ((Layout.degree s (x.1.2.getD x.2 (false,[])).2.length).placeVertices
        (Renderer.offset x.1 x.2) (x.1.2.getD x.2 (false,[])).2)) := by
  let code := ifComputes (eq degree (nat rowEncoding 0)) (low s 0)
    (ifComputes (eq degree (nat rowEncoding 1)) (low s 1)
      (ifComputes (eq degree (nat rowEncoding 2)) (low s 2)
        (ifComputes (eq degree (nat rowEncoding 3)) (low s 3) (high s))))
  exact congrComputes code (fun x => by
    generalize hd : (x.1.2.getD x.2 (false,[])).2.length=d
    simp only [List.getD] at hd
    by_cases h : d≤3
    · interval_cases d <;> simp [Layout.degree,h,hd]
    · have h0 : d≠0 := by omega
      have h1 : d≠1 := by omega
      have h2 : d≠2 := by omega
      have h3 : d≠3 := by omega
      simp [Layout.degree,h,hd,h0,h1,h2,h3])
def placedBytes : Computes rowEncoding Frame.wordEncoding
    (fun x : Row => FixedGadgetSubstitution.Compiler.entries RawClosedNetwork.vertexEncoding (placed x.1 x.2)) :=
  congrComputes (ifComputes side (fixedSide true) (fixedSide false)) (fun x => by
    cases hs : (x.1.2.getD x.2 (false,[])).1 <;>
      simp only [List.getD] at hs <;> simp [placed,hs])
def vertexBytes : Computes argsEncoding Frame.wordEncoding
    (fun x : Args => FixedGadgetSubstitution.Compiler.entries RawClosedNetwork.vertexEncoding (vertices x)) :=
  congrComputes (rangeWordsComputes argsEncoding (fun x : Args => x.2.length)
    (arrays.andThen (WireLists.lengthComputes entryEncoding)) _ placedBytes)
    (fun _ => by simp [vertices,FixedGadgetSubstitution.Compiler.entries,List.flatMap_assoc])
def vertexList : Computes argsEncoding (framedListEncoding RawClosedNetwork.vertexEncoding) vertices :=
  recode (joinComputes vertexBytes (constantComputes argsEncoding Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun x => by
      simpa only [Frame.wordEncoding,framedListEncoding,framedListEncode,List.append_nil,id_eq] using
        entries_append_encode RawClosedNetwork.vertexEncoding (vertices x) [])
def count : Computes argsEncoding unary edgeCount :=
  congrComputes ((pairComputes (identityComputes argsEncoding)
    (arrays.andThen (WireLists.lengthComputes entryEncoding))).andThen offset)
    (fun x => by simp [Renderer.offset,edgeCount,prefix_length])
def rawComputes : Computes argsEncoding RawClosedNetwork.encoding raw :=
  recode (pairComputes vertexList (count.andThen (WireLists.replicate encodingNatBool 0)))
    id (fun _ => rfl) (fun _ => rfl)
def sideTable (s : Bool) : Computes unitEncoding tableEncoding
    (fun g : UnitInput => (List.range g.val.1).map (fun r => (s,OldCompiler.ports g s r))) := by
  let attach : Computes portEncoding entryEncoding (fun ps : List RawEndpoint => (s,ps)) :=
    pairComputes (constantComputes portEncoding encodingBoolBool s) (identityComputes portEncoding)
  exact congrComputes
    ((Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Programs.sidePorts s).andThen
      (WireLists.mapComputes portEncoding entryEncoding (fun ps => (s,ps)) attach))
    (fun _ => by simp [List.map_map,Function.comp_def])
def prepare : Computes unitEncoding argsEncoding args :=
  congrComputes (pairComputes
    Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Programs.edgeCount
    ((pairComputes (sideTable false) (sideTable true)).andThen (WireLists.append entryEncoding)))
    (fun g => by simp [args,OldCompiler.nodes,List.map_append,List.map_map,Function.comp_def])
def computes : Computes unitEncoding (RawClosedNetwork.validatedEncoding 2 1 arity) Layout.query :=
  recode (congrComputes (prepare.andThen rawComputes) raw_unit)
    id (fun _ => rfl) (fun _ => rfl)
theorem query_execution (g : UnitInput) : Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Programs.RunsExactly computes.machine.computer.step
    (initList computes.machine.computer (unitEncoding.encode g))
    (haltList computes.machine.computer (Layout.queryBits g)) (computes.outputs g).steps :=
  (computes.outputs g).evals_in_steps
theorem query_time (g : UnitInput) :
    (computes.outputs g).steps≤computes.time.eval (unitEncoding.encode g).length :=
  (computes.outputs g).steps_le_m
theorem query_primitive (g : UnitInput) : primitiveCost computes.machine (computes.outputs g).steps
    (some (initList computes.machine.computer (unitEncoding.encode g)))≤
      (primitivePolynomial computes).eval (unitEncoding.encode g).length := computes_primitive_cost computes g
theorem query_storage (g : UnitInput) (t : ℕ) (c : computes.machine.Config)
    (ht : t≤computes.time.eval (unitEncoding.encode g).length)
    (hr : Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Programs.RunsExactly computes.machine.computer.step (initList computes.machine.computer (unitEncoding.encode g)) c t) :
    stackSize c.stk≤computes.outputBound.bound.eval (unitEncoding.encode g).length := by
  have h := computes.machine.run_size_le _ _ _ hr
  rw [Machine.size_init] at h
  exact h.trans (by
    simpa only [Computes.outputBound,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C] using
        Nat.add_le_add_left (Nat.mul_le_mul_right computes.machine.primitiveBudget ht) (unitEncoding.encode g).length)

end Code
end Renderer
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
