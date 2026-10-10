import Holant.Proofs.Hardness.GeneralEOSignedNativeRaw
import Holant.Proofs.Hardness.GeneralEOPairedFamilySigned

/-! The fixed signed palette contains all sign words of each original row.
The actual native input only selects those fixed labels and writes component
addresses. Nullary rows retain one occurrence in the emitted label list. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeQuery
open Computability Holant Holant.Tractable Holant.Complexity
namespace R
export GeneralEOSignedNativeRaw (Input parsed rowPairing)
end R
namespace D
export GeneralEOSignedNativeDecoded (label pairing signedQueryValue nativeValue)
end D
namespace N
export GeneralEOSignedNativeParity (signedScope)
end N
namespace S
export GeneralEOPairedFamilySigned (pairing value signed_compressed)
end S
namespace F
export GeneralEOPairedCSPFamilyRaw (Raw)
end F
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))

abbrev Palette := Σ i : Fin s, Fin (P i).count → Bool
def count : ℕ := Fintype.card (Palette P)
def enumeration : Palette P ≃ Fin (count P) := Fintype.equivFin (Palette P)
def label (i : Fin (count P)) : Fin s := ((enumeration P).symm i).1
def signs (i : Fin (count P)) : Fin (P (label P i)).count → Bool := ((enumeration P).symm i).2

def rowSigns (r : R.Input (s:=s) (arity:=arity)) (v : Fin r.val.vertices.length) :
    Fin (P (D.label r v)).count → Bool :=
  fun j => (N.signedScope (r.val.shape r.property) (R.rowPairing P r) v j).2

def rowLabel (r : R.Input (s:=s) (arity:=arity)) (v : Fin r.val.vertices.length) : Fin (count P) :=
  enumeration P ⟨D.label r v,rowSigns P r v⟩

def rowScopes (r : R.Input (s:=s) (arity:=arity)) (v : Fin r.val.vertices.length) : List ℕ :=
  List.ofFn (fun j => (N.signedScope (r.val.shape r.property) (R.rowPairing P r) v j).1.val)

def query (r : R.Input (s:=s) (arity:=arity)) : F.Raw (count P) :=
  ⟨r.val.edges.length*2,List.ofFn (rowLabel P r),
    (List.finRange r.val.vertices.length).flatMap (rowScopes P r)⟩

@[simp] theorem label_row (r : R.Input (s:=s) (arity:=arity)) (v : Fin r.val.vertices.length) :
    label P (rowLabel P r v)=D.label r v := by simp [label,rowLabel]

@[simp] theorem count_row (r : R.Input (s:=s) (arity:=arity)) (v : Fin r.val.vertices.length) :
    (S.pairing P (label P) (signs P) (rowLabel P r v)).count=(P (D.label r v)).count := by
  change (P (label P (rowLabel P r v))).count=_
  rw [label_row]

theorem rows_preserved (r : R.Input (s:=s) (arity:=arity)) :
    (query P r).labels.length=r.val.vertices.length := by simp [query]

theorem original_labels (r : R.Input (s:=s) (arity:=arity)) :
    (query P r).labels.map (label P)=List.ofFn (D.label r) := by
  simp [query,List.map_ofFn,Function.comp_def]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeQuery
