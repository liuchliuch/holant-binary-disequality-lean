import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSemantics
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativePhaseBundleProgramme

/-! Concrete conversion of validated ordinary CSP factor records to the
heterogeneous flat CSP codec. Existing validity reflects natural labels into
Fin; the actual programme copies their unchanged bytes and flattens ordered
scopes. No nonempty-label-family assumption is needed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockInput
open Holant Holant.Tractable Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace S
export StableHigherCurrentOrdinarySquareProgramme (Input inputEncoding variablesComputes factorsComputes)
end S
namespace D
export OrdinaryNegativeMixedBlockData (family factor Input inputEncoding)
end D
namespace C
export GeneralEOPairedCSPFamilyRaw (Raw value labelEncoding labelsEncoding addressesEncoding)
end C
namespace W
export StableHigherCurrentOrdinarySquare (value weight extend)
end W
namespace F
export GeneralEOPairedFamilyExtractionWriter (weight)
end F
namespace Pn
export GeneralEOPairedFamilyExtractionPinRaw (value_eq weight)
end Pn
namespace L
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (mapComputes flatten)
end L
namespace P
export OrdinaryNegativePhaseBundleProgramme (labelComputes scopeComputes)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

variable {u : ℕ} {a : ℕ → ℕ}

def typedRow (r : S.Input u a) (v : Fin r.val.factors.length) : Fin u×List ℕ :=
  (⟨(r.val.factors.get v).1,(r.property _ (List.get_mem _ _)).1⟩,(r.val.factors.get v).2)

def typedRows (r : S.Input u a) : List (Fin u×List ℕ) := List.ofFn (typedRow r)

theorem typedRows_factor (r : S.Input u a) : (typedRows r).map D.factor=r.val.factors := by
  rw [typedRows,List.map_ofFn]
  have he : D.factor ∘ typedRow r=r.val.factors.get := by
    funext v
    rfl
  rw [he,List.ofFn_get]

theorem typedRows_addresses (r : S.Input u a) :
    (typedRows r).flatMap Prod.snd=r.val.factors.flatMap Prod.snd := by
  have h := congrArg (fun rows : List Factor => rows.flatMap Prod.snd) (typedRows_factor r)
  simpa only [List.flatMap_map,D.factor,Function.comp_def] using h

theorem typedRows_labels (r : S.Input u a) :
    ((typedRows r).map Prod.fst).map Fin.val=r.val.factors.map Prod.fst := by
  have h := congrArg (fun rows : List Factor => rows.map Prod.fst) (typedRows_factor r)
  simpa only [List.map_map,D.factor,Function.comp_def] using h

theorem typedRows_lengths (r : S.Input u a) :
    ∀row∈typedRows r,row.2.length=(D.family u a row.1).count := by
  intro row hr
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hr
  exact (r.property _ (List.get_mem _ _)).2.1

def raw (r : S.Input u a) : C.Raw u :=
  ⟨r.val.variables,(typedRows r).map Prod.fst,r.val.factors.flatMap Prod.snd⟩

theorem wellFormed (r : S.Input u a) :
    (raw r).WellFormed (arity:=fun k=>a k*2) (D.family u a) := by
  constructor
  · change (r.val.factors.flatMap Prod.snd).length=
      (((typedRows r).map Prod.fst).map (fun i => (D.family u a i).count)).sum
    rw [←typedRows_addresses r,List.length_flatMap,List.map_map]
    congr 1
    apply List.map_congr_left
    intro row hr
    exact typedRows_lengths r row hr
  · intro k hk
    obtain ⟨row,hr,hk⟩ := List.mem_flatMap.mp hk
    exact (r.property row hr).2.2 k hk

def query (r : S.Input u a) : D.Input (u:=u) (a:=a) := ⟨raw r,wellFormed r⟩

@[simp] theorem variables_same (r : S.Input u a) : (query r).val.variables=r.val.variables := rfl
@[simp] theorem addresses_same (r : S.Input u a) :
    (query r).val.addresses=r.val.factors.flatMap Prod.snd := rfl

theorem labels_same (r : S.Input u a) :
    (query r).val.labels.map Fin.val=r.val.factors.map Prod.fst := typedRows_labels r

/-- The target Fin-label codec is literally the original natural-label codec. -/
theorem label_encode (i : Fin u) :
    (C.labelEncoding u).encode i=encodingNatBool.encode i.val := rfl

theorem labels_encode (ls : List (Fin u)) :
    (framedListEncoding (C.labelEncoding u)).encode ls=
      (framedListEncoding encodingNatBool).encode (ls.map Fin.val) := by
  induction ls with
  | nil => rfl
  | cons i ls ih =>
      simpa only [framedListEncoding,framedListEncode,List.map_cons,label_encode] using
        congrArg (fun tail => true::(Holant.Algebraic.frame (encodingNatBool.encode i.val)++tail)) ih

abbrev fieldsEncoding := pairEncoding UnaryBinary.unaryEncoding
  (pairEncoding (framedListEncoding encodingNatBool) C.addressesEncoding)

def fields (r : Raw) : ℕ×(List ℕ×List ℕ) :=
  (r.variables,(r.factors.map Prod.fst,r.factors.flatMap Prod.snd))

def labelsComputes : Computes Raw.encoding (framedListEncoding encodingNatBool)
    (fun r => r.factors.map Prod.fst) :=
  S.factorsComputes.andThen (L.mapComputes Raw.factorEncoding encodingNatBool Prod.fst P.labelComputes)

def addressesComputes : Computes Raw.encoding C.addressesEncoding
    (fun r => r.factors.flatMap Prod.snd) :=
  congrComputes ((S.factorsComputes.andThen
    (L.mapComputes Raw.factorEncoding C.addressesEncoding Prod.snd P.scopeComputes)).andThen
      (L.flatten encodingNatBool)) (fun _ => by simp only [List.flatMap_def,Function.comp_def])

/-- Actual map/flatten machines produce all three physical output fields. -/
def fieldsComputes : Computes Raw.encoding fieldsEncoding fields :=
  pairComputes S.variablesComputes (pairComputes labelsComputes addressesComputes)

theorem query_encode (r : S.Input u a) :
    fieldsEncoding.encode (fields r.val)=(D.inputEncoding (u:=u) (a:=a)).encode (query r) := by
  change (pairEncoding UnaryBinary.unaryEncoding
    (pairEncoding (framedListEncoding encodingNatBool) C.addressesEncoding)).encode
      (r.val.variables,(r.val.factors.map Prod.fst,r.val.factors.flatMap Prod.snd))=
    (pairEncoding UnaryBinary.unaryEncoding
      (pairEncoding (C.labelsEncoding u) C.addressesEncoding)).encode
        (r.val.variables,((typedRows r).map Prod.fst,r.val.factors.flatMap Prod.snd))
  simp only [pairEncoding_encode,labels_encode,typedRows_labels]

/-- Semantic validity changes only the specification type: emitted label
bytes are unchanged, including when the source label family is empty. -/
def queryComputes : Computes (S.inputEncoding u a) (D.inputEncoding (u:=u) (a:=a)) query :=
  recode fieldsComputes Subtype.val (fun _ => rfl) query_encode

variable {K : Type} [CommSemiring K] (H : (i : Fin u) → Signature K (a i.val))

/-- Every original row, including nullary rows, retains its exact factor;
all declared variables, including unused ones, retain their assignment sum. -/
theorem value (r : S.Input u a) :
    C.value (s:=u) (arity:=fun k => a k*2) (D.family u a) H (query r).val=W.value H r.val := by
  rw [Pn.value_eq (s:=u) (arity:=fun k => a k*2) (D.family u a) H]
  unfold W.value
  apply Finset.sum_congr rfl
  intro x _
  change F.weight (s:=u) (arity:=fun k => a k*2) (D.family u a) H
    ((typedRows r).map Prod.fst)
    (fun k => W.extend x ((r.val.factors.flatMap Prod.snd).getD k 0))=
      W.weight H r.val.factors (W.extend x)
  rw [←typedRows_addresses r,OrdinaryNegativeMixedBlockSemantics.weight_data H
    (typedRows r) (typedRows_lengths r),typedRows_factor]

/-- The scalar-correction count is preserved without constructing Fin u's zero. -/
theorem label_zero_count (r : S.Input u a) :
    ((query r).val.labels.filter (fun i => i.val=0)).length=
      OrdinaryNegativePhaseBundleRaw.copies r.val := by
  have h := congrArg (fun labels : List ℕ => (labels.filter (fun i => i=0)).length) (labels_same r)
  simpa only [List.filter_map,List.length_map,Function.comp_def,OrdinaryNegativePhaseBundleRaw.copies] using h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockInput
end
