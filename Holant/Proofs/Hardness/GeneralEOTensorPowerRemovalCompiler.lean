import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalRaw
import Holant.Proofs.Hardness.PairedPinsCompiler
import Holant.Proofs.BinaryInterpolation.SingularExtraction.UnaryQuotient

/-! The general tensor grouping compiler is an actual finite Boolean-stack
programme over the original framed raw-network codec. It scans selected rows,
computes their unary count and fixed-modulus quotient, emits k literal row-port
lists per block using bounded lookup, and copies the original edge stream. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalCompiler
open Turing Computability Holant Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open GeneralEOTensorPowerRemovalRaw
namespace P
export PairedPinsCompiler (rowEncoding rowsEncoding portsEncoding edgesEncoding rawEncoding
  rowsComputes edgesComputes pinTest singletonRow oldRowsComputes portsComputes)
end P
namespace U
export Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.UnaryQuotient
  (computes timesComputes addConstantComputes)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
abbrev unary := UnaryBinary.unaryEncoding
abbrev cellEncoding := pairEncoding P.rawEncoding unary

def keepSelected (s : ℕ) : Computes P.rowEncoding P.rowsEncoding
    (fun v=>if v.1=s then [v] else []) :=
  congrComputes (ifComputes (P.pinTest s false) P.singletonRow
    (constantComputes P.rowEncoding P.rowsEncoding [])) (fun v=>by simp)

theorem selected_flatMap (s : ℕ) (xs : List RawVertex) :
    xs.flatMap (fun v=>if v.1=s then [v] else [])=xs.filter (fun v=>v.1=s) := by
  induction xs with
  | nil => rfl
  | cons v xs ih => by_cases h : v.1=s <;> simp [h,ih]

def selectedComputes (s : ℕ) : Computes P.rawEncoding P.rowsEncoding (selected s) :=
  congrComputes (P.rowsComputes.andThen
    (AccessPrograms.flatMap P.rowEncoding P.rowEncoding _ (keepSelected s)))
    (fun r=>selected_flatMap s r.vertices)

def countComputes (s : ℕ) : Computes P.rawEncoding unary (count s) :=
  (selectedComputes s).andThen (WireLists.lengthComputes P.rowEncoding)

def blockCountComputes (s k : ℕ) (hk : 0<k) : Computes P.rawEncoding unary
    (fun r=>count s r/k) := (countComputes s).andThen (U.computes k hk)

def blockRow (s k : ℕ) (r : RawClosedNetwork) (i : ℕ) : RawVertex :=
  (s,((List.range k).map (fun j=>(selected s r).getD (k*i+j) (0,[]))).flatMap Prod.snd)

def rowAtComputes (s k j : ℕ) : Computes cellEncoding P.rowEncoding
    (fun x=>(selected s x.1).getD (k*x.2+j) (0,[])) :=
  AccessPrograms.get P.rowEncoding (0,[])
    ((Wiring.firstComputes P.rawEncoding unary).andThen (selectedComputes s))
    (((Wiring.secondComputes P.rawEncoding unary).andThen (U.timesComputes k)).andThen
      (U.addConstantComputes j))

def blockRowComputes (s k : ℕ) : Computes cellEncoding P.rowEncoding
    (fun x=>blockRow s k x.1 x.2) := by
  let ports := (fixedListComputes cellEncoding P.portsEncoding
    (fun x j=>((selected s x.1).getD (k*x.2+j) (0,[])).2)
    (fun j=>(rowAtComputes s k j).andThen P.portsComputes) (List.range k)).andThen
      (WireLists.flatten RawClosedNetwork.endpointEncoding)
  exact recode (pairComputes (constantComputes cellEncoding encodingNatBool s) ports)
    id (fun _=>rfl) (fun _=>by simp only [blockRow,List.flatMap_def,List.map_map,Function.comp_def,id_eq]; rfl)

theorem blocks_indexed {α : Type*} (k q : ℕ) (xs : List α) :
    blocks k q xs=(List.range q).map (fun i=>(xs.drop (k*i)).take k) := by
  induction q generalizing xs with
  | zero => rfl
  | succ q ih =>
    simp [blocks,List.range_succ_eq_map,ih,List.map_map,Function.comp_def,
      List.drop_drop,Nat.mul_add,Nat.add_comm]

theorem indexed_block {α : Type*} (xs : List α) (k i : ℕ) (d : α)
    (hi : i<xs.length/k) :
    (List.range k).map (fun j=>xs.getD (k*i+j) d)=(xs.drop (k*i)).take k := by
  have hq := Nat.div_mul_le_self xs.length k
  have hm := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul,Nat.mul_comm i k] at hm
  have hb : k*i+k≤xs.length := by omega
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_take,List.length_drop]
    omega
  · intro j hj ht
    have hj' : j<k := by simpa using hj
    have hlt : k*i+j<xs.length := by omega
    simp only [List.getElem_map,List.getElem_range,List.getElem_take,List.getElem_drop]
    exact List.getD_eq_getElem xs d hlt

theorem blockRows_eq (s k : ℕ) (r : RawClosedNetwork) :
    (List.range (count s r/k)).map (blockRow s k r)=groupedRows s k r := by
  rw [groupedRows,blocks_indexed,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hb : i<(selected s r).length/k := List.mem_range.mp hi
  exact Prod.ext rfl (congrArg (List.flatMap Prod.snd) (indexed_block _ k i (0,[]) hb))

def groupedRowsComputes (s k : ℕ) (hk : 0<k) :
    Computes P.rawEncoding P.rowsEncoding (groupedRows s k) :=
  congrComputes (WireLists.tabulate P.rawEncoding P.rowEncoding (fun r=>count s r/k)
    (blockCountComputes s k hk) (blockRow s k) (blockRowComputes s k))
    (blockRows_eq s k)

def verticesComputes (s k : ℕ) (hk : 0<k) : Computes P.rawEncoding P.rowsEncoding
    (fun r=>(raw s k r).vertices) :=
  (pairComputes (P.oldRowsComputes s) (groupedRowsComputes s k hk)).andThen
    (WireLists.append P.rowEncoding)

/-- No divisibility premise is used to obtain execution or polynomial time. -/
def computes (s k : ℕ) (hk : 0<k) : Computes P.rawEncoding P.rawEncoding (raw s k) :=
  recode (pairComputes (verticesComputes s k hk) P.edgesComputes) id (fun _=>rfl) (fun _=>rfl)

abbrev Input (s b n k : ℕ) (a : ℕ→ℕ) :=
  {r : RawClosedNetwork // r.WellFormed (s+1) b (sourceArity s n a) ∧ count s r%k=0}

def inputEncoding (s b n k : ℕ) (a : ℕ→ℕ) : Encoding (Input s b n k a) Bool where
  encode r:=RawClosedNetwork.encoding.encode r.val
  decode bits:=(RawClosedNetwork.encoding.decode bits).bind fun r=>
    if h : r.WellFormed (s+1) b (sourceArity s n a) ∧ count s r%k=0 then some ⟨r,h⟩ else none
  decode_encode r:=by simp [r.property]

def query {s b n k : ℕ} {a : ℕ→ℕ} (r : Input s b n k a) :
    {q : RawClosedNetwork // q.WellFormed (s+1) b (targetArity s n k a)} :=
  ⟨raw s k r.val,wellFormed r.property.1 r.property.2⟩

/-- The same output bytes carry the proved actual closed-graph validator. -/
def validatedComputes (s b n k : ℕ) (a : ℕ→ℕ) (hk : 0<k) :
    Computes (inputEncoding s b n k a)
      (RawClosedNetwork.validatedEncoding (s+1) b (targetArity s n k a)) query :=
  recode (computes s k hk) Subtype.val (fun _=>rfl) (fun _=>rfl)

theorem output_length (s k : ℕ) (hk : 0<k) (r : RawClosedNetwork) :
    (P.rawEncoding.encode (raw s k r)).length≤
      (computes s k hk).outputBound.bound.eval (P.rawEncoding.encode r).length :=
  (computes s k hk).outputBound.length_le r

theorem primitive_cost (s k : ℕ) (hk : 0<k) (r : RawClosedNetwork) :
    primitiveCost (computes s k hk).machine ((computes s k hk).outputs r).steps
      (some (initList (computes s k hk).machine.computer (P.rawEncoding.encode r)))≤
      (primitivePolynomial (computes s k hk)).eval (P.rawEncoding.encode r).length :=
  computes_primitive_cost (computes s k hk) r

theorem prefix_storage (s k : ℕ) (hk : 0<k) (r : RawClosedNetwork) (t : ℕ)
    (ht : t≤((computes s k hk).outputs r).steps) (z : (computes s k hk).machine.Config)
    (hr : (fun q=>q.bind (computes s k hk).machine.computer.step)^[t]
      (some (initList (computes s k hk).machine.computer (P.rawEncoding.encode r)))=some z) :
    stackSize z.stk≤(P.rawEncoding.encode r).length+
      (computes s k hk).time.eval (P.rawEncoding.encode r).length*(computes s k hk).machine.primitiveBudget := by
  have hs := (computes s k hk).machine.run_size_le _ z t hr
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _
    (ht.trans ((computes s k hk).outputs r).steps_le_m)) _)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalCompiler
