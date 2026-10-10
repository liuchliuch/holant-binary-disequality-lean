import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyProgramme
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionTensor

/-! Literal expansion of a disjoint tensor CSP row into its two original
family labels. The byte programme retains variable declarations and every
address, including repeated addresses, unused variables and nullary rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionWriter
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open scoped BigOperators
namespace R
export GeneralEOPairedCSPRaw (Raw encoding fieldsEncoding variablesComputes constraintsComputes addressesComputes read)
end R
namespace F
export GeneralEOPairedCSPFamilyRaw (Raw encoding fieldsEncoding labelEncoding labelsEncoding addressesEncoding value)
end F
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (replicate flatten)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ → ℕ} (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (left right : Fin s)

/-- Exactly two original labels per input constraint, in source factor order. -/
def labels (count : ℕ) : List (Fin s) := (List.replicate count [left,right]).flatten

@[simp] theorem labels_zero : labels left right 0=[] := rfl
@[simp] theorem labels_succ (count : ℕ) :
    labels left right (count+1)=left::right::labels left right count := by
  simp [labels, List.replicate_succ]

def query (r : R.Raw) : F.Raw s := ⟨r.variables,labels left right r.constraints,r.addresses⟩

def labelsComputes : Computes R.encoding (F.labelsEncoding s) (fun r => labels left right r.constraints) :=
  R.constraintsComputes.andThen
    ((W.replicate (F.labelsEncoding s) [left,right]).andThen (W.flatten (F.labelEncoding s)))

/-- The actual finite Boolean-stack programme writes the target's existing
raw-family codec; there is no assumed row compiler or changed answer codec. -/
def queryComputes : Computes R.encoding (F.encoding s) (query left right) :=
  recode (pairComputes R.variablesComputes
    (pairComputes (labelsComputes left right) R.addressesComputes)) id
    (fun _ => rfl) (fun _ => rfl)

theorem counts (r : R.Raw) : (query left right r).labels.length=2*r.constraints ∧
    (query left right r).variables=r.variables ∧ (query left right r).addresses=r.addresses := by
  refine ⟨?_,rfl,rfl⟩
  simp [query, labels, List.length_flatten, List.map_replicate, List.sum_replicate, Nat.mul_comm]

theorem edgeCount (r : R.Raw) :
    (query left right r).edgeCount P=r.constraints*((P left).count+(P right).count) := by
  change ((labels left right r.constraints).map (fun i => (P i).count)).sum = _
  induction r.constraints with
  | zero => simp
  | succ c ih => simp [ih, Nat.add_mul, Nat.add_assoc, Nat.add_comm]

theorem wellFormed_iff (r : R.Raw) :
    (query left right r).WellFormed P ↔ r.WellFormed ((P left).count+(P right).count) := by
  change ((query left right r).addresses.length = (query left right r).edgeCount P ∧
    ∀v ∈ (query left right r).addresses, v < (query left right r).variables) ↔ _
  rw [edgeCount]
  rfl

variable {K : Type*} [CommSemiring K]
variable (g : (i : Fin s) → Signature K (P i).count)

/-- Assignment weight of a raw label list, with an arbitrary address reader. -/
def weight (ls : List (Fin s)) (a : ℕ → Bool) : K :=
  ∏v : Fin ls.length, g (ls.get v)
    (fun j => a (((ls.map (fun i => (P i).count)).take v.val).sum+j.val))

@[simp] theorem weight_nil (a : ℕ → Bool) : weight P g [] a=1 := by simp [weight]

theorem weight_cons (i : Fin s) (ls : List (Fin s)) (a : ℕ → Bool) :
    weight P g (i::ls) a=g i (fun j => a j.val)*
      weight P g ls (fun k => a ((P i).count+k)) := by
  unfold weight
  simp only [List.length_cons]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, List.take_zero, List.sum_nil, zero_add,
    List.get_cons_zero, List.map_cons, Fin.val_succ, List.get_cons_succ',
    List.take_succ_cons, List.sum_cons, Nat.add_assoc]

def tensor {m n : ℕ} (f : Signature K m) (h : Signature K n) : Signature K (m+n) :=
  Tensor.reindex finSumFinEquiv (Tensor.tensor f h)

theorem weight_labels (count : ℕ) (a : ℕ → Bool) :
    weight P g (labels left right count) a =
      ∏v : Fin count, tensor (g left) (g right)
        (fun j => a (v.val*((P left).count+(P right).count)+j.val)) := by
  induction count generalizing a with
  | zero => simp
  | succ c ih =>
    rw [labels_succ, weight_cons, weight_cons, ih, Fin.prod_univ_succ]
    simp only [Fin.val_zero, zero_mul, zero_add, tensor, Tensor.reindex, Tensor.tensor,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
    rw [mul_assoc]
    apply congrArg ((g left (fun j => a j.val)) * ·)
    apply congrArg ((g right (fun j => a ((P left).count+j.val))) * ·)
    apply Finset.prod_congr rfl
    intro v _
    congr 2 <;> funext j <;> congr 1 <;> simp only [Fin.val_succ, Nat.add_mul, one_mul] <;> omega

/-- Existing raw single-signature records, with an arbitrary actual arity. -/
def rawValue {n : ℕ} (h : Signature K n) (r : R.Raw) : K :=
  ∑x : Fin r.variables → Bool, ∏v : Fin r.constraints,
    h (fun j => R.read x (r.addresses.getD (v.val*n+j.val) 0))

/-- Assignment-by-assignment equality. The statement deliberately includes
malformed records; validation is dealt with separately by wellFormed_iff. -/
theorem query_value (r : R.Raw) :
    F.value P g (query left right r)=rawValue (tensor (g left) (g right)) r := by
  unfold F.value rawValue
  apply Finset.sum_congr rfl
  intro x _
  exact weight_labels P left right g r.constraints
    (fun k => R.read x (r.addresses.getD k 0))

theorem output_bound (r : R.Raw) :
    ((F.encoding s).encode (query left right r)).length ≤
      (queryComputes left right).outputBound.bound.eval (R.encoding.encode r).length :=
  (queryComputes left right).outputBound.length_le r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionWriter
