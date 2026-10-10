import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionRestrictionRaw

/-! Exact assignment and partition identities for the physical minor writer.
Arbitrary repeated addresses, unused free variables and nullary parent rows
are retained. Invalid source records map to one fixed invalid target record. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionRestrictionValue
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open UniversalPairReduction.SmoothingCompiler
open scoped BigOperators
namespace R
export GeneralEOPairedCSPRaw (Raw encoding read)
end R
namespace W
export GeneralEOPairedFamilyExtractionRestrictionRaw (port row addresses raw rawComputes validates addresses_length addresses_lt)
end W
namespace T
export GeneralEOPairedFamilyExtractionWriter (labels query queryComputes weight_labels tensor rawValue)
end T
namespace Pn
export GeneralEOPairedFamilyExtractionPinRaw (free fixed weight anchor)
end Pn
namespace F
export GeneralEOPairedCSPFamilyRaw (Raw encoding)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

private theorem range_map_eq_ofFn {α : Type*} (c : ℕ) (f : ℕ → α) :
    (List.range c).map f=List.ofFn (fun i : Fin c => f i.val) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

private theorem flatten_ofFn_getD {α : Type*} (d : α) {c n : ℕ}
    (a : Fin c → Fin n → α) (v : Fin c) (j : Fin n) :
    ((List.ofFn (fun i => List.ofFn (a i))).flatten).getD (v.val*n+j.val) d=a v j := by
  induction c with
  | zero => exact Fin.elim0 v
  | succ c ih =>
    rw [List.ofFn_succ,List.flatten_cons]
    refine Fin.cases ?_ (fun v => ?_) v
    · rw [List.getD_append _ _ _ _ (by simp)]
      simp
    · have he : (v.succ.val*n+j.val)-n=v.val*n+j.val := by simp only [Fin.val_succ,Nat.succ_mul]; omega
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn,Fin.val_succ,Nat.succ_mul]; omega),List.length_ofFn,he]
      exact ih (fun k => a k.succ) v

variable {m n : ℕ} (p : Fin n → Bool ⊕ Fin m)

theorem addresses_at (r : R.Raw) (v : Fin r.constraints) (j : Fin n) :
    (W.addresses p r).getD (v.val*n+j.val) 0=W.port r v.val (p j) := by
  rw [W.addresses,range_map_eq_ofFn]
  exact flatten_ofFn_getD 0 (fun i j => W.port r i.val (p j)) v j

theorem anchor_port (r : R.Raw) (x : Fin r.variables → Bool) (v : ℕ) (q : Bool ⊕ Fin m) :
    Pn.anchor false true x (W.port r v q)=
      Sum.elim id (fun j : Fin m => R.read x (r.addresses.getD (v*m+j.val) 0)) q := by
  cases q with
  | inl b => cases b <;> rfl
  | inr j => rfl

variable {s : ℕ} {arity : ℕ → ℕ} (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (left right : Fin s)
variable (q : Fin ((P left).count+(P right).count) → Bool ⊕ Fin m)

def query (r : R.Raw) : F.Raw s := T.query left right (W.raw q r)

def queryComputes : Computes R.encoding (F.encoding s) (query P left right q) :=
  (W.rawComputes q).andThen (T.queryComputes left right)

theorem query_valid (r : R.Raw) (hr : r.WellFormed m) :
    (Pn.free (query P left right q r)).WellFormed P := by
  constructor
  · change (W.addresses q r).length=(T.labels left right r.constraints |>.map (fun i => (P i).count)).sum
    rw [W.addresses_length]
    exact (GeneralEOPairedFamilyExtractionWriter.edgeCount P left right (W.raw q r)).symm
  · exact W.addresses_lt q r hr

variable {K : Type*} [CommSemiring K]
variable (g : (i : Fin s) → Signature K (P i).count)

def minor : Signature K m := fun z => T.tensor (g left) (g right)
  (GeneralEOPairedFamilyExtractionTensor.substitute q z)

theorem query_value (r : R.Raw) :
    Pn.fixed P g (query P left right q r) false true=T.rawValue (minor P left right q g) r := by
  unfold Pn.fixed T.rawValue
  change (∑x : Fin r.variables → Bool, Pn.weight P g (query P left right q r)
    (Pn.anchor false true x))=_
  apply Finset.sum_congr rfl
  intro x _
  change GeneralEOPairedFamilyExtractionWriter.weight P g (T.labels left right r.constraints)
    (fun k => Pn.anchor false true x ((W.addresses q r).getD k 0))=_
  rw [T.weight_labels]
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext j
  rw [addresses_at,anchor_port]
  rfl

/-- This sentinel is malformed for every family and every pairing, including
an empty family and nullary labels. -/
def rejected : F.Raw s := ⟨0,[],[0]⟩

theorem rejected_invalid : ¬(Pn.free (rejected (s:=s))).WellFormed P := by
  intro h
  have hh := h.1
  simp [rejected,Pn.free,GeneralEOPairedCSPFamilyRaw.Raw.edgeCount] at hh

def validatedQuery (r : R.Raw) : F.Raw s :=
  if r.WellFormed m then query P left right q r else rejected

def validatedComputes : Computes R.encoding (F.encoding s) (validatedQuery P left right q) :=
  congrComputes (ifComputes (W.validates (m:=m)) (queryComputes P left right q)
    (constantComputes R.encoding (F.encoding s) rejected)) (fun r => by simp [validatedQuery])

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionRestrictionValue
