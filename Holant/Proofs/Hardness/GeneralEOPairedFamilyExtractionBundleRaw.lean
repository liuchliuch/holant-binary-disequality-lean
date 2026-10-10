import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionRestrictionValue

/-! Physical concatenation of a fixed list of literal minors at each CSP
constraint. All emitted vertices use the two internally selected original
labels; reference pins and declared free variables have the accepted codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionBundleRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
namespace F
export GeneralEOPairedCSPFamilyRaw (Raw encoding unary labelsEncoding labelEncoding addressesEncoding
  variablesComputes labelsComputes addressesComputes)
end F
namespace R
export GeneralEOPairedCSPRaw (Raw encoding variablesComputes)
end R
namespace V
export GeneralEOPairedFamilyExtractionRestrictionValue (query queryComputes query_valid)
end V
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (append)
end W
namespace Pn
export GeneralEOPairedFamilyExtractionPinRaw (free)
end Pn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ}

def append (r t : F.Raw s) : F.Raw s :=
  ⟨r.variables,r.labels++t.labels,r.addresses++t.addresses⟩

abbrev inputEncoding (s : ℕ) := pairEncoding (F.encoding s) (F.encoding s)

def appendComputes : Computes (inputEncoding s) (F.encoding s)
    (fun x : F.Raw s×F.Raw s => append x.1 x.2) :=
  recode (pairComputes ((Wiring.firstComputes (F.encoding s) (F.encoding s)).andThen F.variablesComputes)
    (pairComputes
      ((pairComputes ((Wiring.firstComputes (F.encoding s) (F.encoding s)).andThen F.labelsComputes)
        ((Wiring.secondComputes (F.encoding s) (F.encoding s)).andThen F.labelsComputes)).andThen
          (W.append (F.labelEncoding s)))
      ((pairComputes ((Wiring.firstComputes (F.encoding s) (F.encoding s)).andThen F.addressesComputes)
        ((Wiring.secondComputes (F.encoding s) (F.encoding s)).andThen F.addressesComputes)).andThen
          (W.append encodingNatBool)))) id (fun _ => rfl) (fun _ => rfl)

variable {arity : ℕ → ℕ} (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))

theorem append_valid (r t : F.Raw s) (hr : (Pn.free r).WellFormed P)
    (ht : (Pn.free t).WellFormed P) (he : r.variables=t.variables) :
    (Pn.free (append r t)).WellFormed P := by
  constructor
  · change (r.addresses++t.addresses).length=((r.labels++t.labels).map (fun i => (P i).count)).sum
    rw [List.length_append,List.map_append,List.sum_append]
    exact congrArg₂ (·+·) hr.1 ht.1
  · intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact hr.2 a ha
    · simpa only [Pn.free,append,he] using ht.2 a ha

variable {m : ℕ} (left right : Fin s)
variable (ps : List (Fin ((P left).count+(P right).count) → Bool ⊕ Fin m))

def query (ps : List (Fin ((P left).count+(P right).count) → Bool ⊕ Fin m)) (r : R.Raw) : F.Raw s :=
  match ps with
  | [] => ⟨r.variables,[],[]⟩
  | p::ps => append (V.query P left right p r) (query ps r)

@[simp] theorem query_variables (r : R.Raw) : (query P left right ps r).variables=r.variables := by
  cases ps <;> rfl

def queryComputes (ps : List (Fin ((P left).count+(P right).count) → Bool ⊕ Fin m)) : Computes R.encoding (F.encoding s) (query P left right ps) :=
  match ps with
  | [] => recode (pairComputes R.variablesComputes
      (constantComputes R.encoding (pairEncoding (F.labelsEncoding s) F.addressesEncoding) ([],[])))
        id (fun _ => rfl) (fun _ => rfl)
  | p::ps => (pairComputes (V.queryComputes P left right p) (queryComputes ps)).andThen appendComputes

theorem query_valid (r : R.Raw) (hr : r.WellFormed m) :
    (Pn.free (query P left right ps r)).WellFormed P := by
  induction ps with
  | nil => exact ⟨rfl,by simp [query,Pn.free]⟩
  | cons p ps ih =>
    exact append_valid P _ _ (V.query_valid P left right p r hr) ih (by rw [query_variables]; rfl)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionBundleRaw
