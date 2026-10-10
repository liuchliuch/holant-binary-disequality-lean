import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionWriter
import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyValidation

/-! Universal reference-variable surgery for arbitrary mixed compressed CSPs.
The source variable count records free variables; addresses 0 and 1 are the
two pinned references and address k+2 is free variable k. The four target
records contain only existing family labels and variable identifications. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPinRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GeneralEOPairedCSPFamilyRaw
open scoped BigOperators
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (mapComputes append succComputes)
export GeneralEOPairedFamilyExtractionWriter (weight weight_cons)
end W
namespace R
export GeneralEOPairedCSPRaw (read)
end R
namespace A
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ → ℕ} (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))

def free (r : Raw s) : Raw s := ⟨r.variables+2,r.labels,r.addresses⟩
def merge (r : Raw s) : Raw s := ⟨r.variables+1,r.labels,r.addresses.map (fun k => k-1)⟩

def freeComputes : Computes (encoding s) (encoding s) (free (s:=s)) :=
  recode (pairComputes ((variablesComputes.andThen W.succComputes).andThen W.succComputes)
    tailComputes) id (fun _ => rfl) (fun _ => rfl)

def predComputes : Computes encodingNatBool encodingNatBool (fun n => n-1) :=
  (pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool encodingNatBool 1)).andThen
      UniversalPairReduction.SmoothingCompiler.Endpoints.subtractComputes

def mergeComputes : Computes (encoding s) (encoding s) (merge (s:=s)) :=
  recode (pairComputes (variablesComputes.andThen W.succComputes)
    (pairComputes labelsComputes (addressesComputes.andThen
      (W.mapComputes encodingNatBool encodingNatBool (fun k => k-1) predComputes))))
    id (fun _ => rfl) (fun _ => rfl)

variable (label : Fin s) (bits : Fin (P label).count → Bool)

def anchorAddresses : List ℕ := List.ofFn (fun j => if bits j then 1 else 0)
def augment (r : Raw s) : Raw s := ⟨r.variables,label::r.labels,anchorAddresses P label bits++r.addresses⟩

def augmentComputes : Computes (encoding s) (encoding s) (augment P label bits) :=
  recode (pairComputes variablesComputes
    (pairComputes ((pairComputes (constantComputes (encoding s) (labelEncoding s) label)
      labelsComputes).andThen (A.cons (labelEncoding s)))
      ((pairComputes (constantComputes (encoding s) addressesEncoding (anchorAddresses P label bits))
        addressesComputes).andThen (W.append encodingNatBool))))
    id (fun _ => rfl) (fun _ => rfl)

theorem free_merge_wellFormed (r : Raw s) (hr : (free r).WellFormed P) :
    (merge r).WellFormed P := by
  constructor
  · exact (List.length_map _).trans hr.1
  · intro v hv
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hv
    have hh := hr.2 k hk
    change k-1<r.variables+1
    change k<r.variables+2 at hh
    omega

theorem free_augment_wellFormed (r : Raw s) (hr : (free r).WellFormed P) :
    (free (augment P label bits r)).WellFormed P := by
  constructor
  · change (anchorAddresses P label bits++r.addresses).length =
      ((label::r.labels).map (fun i => (P i).count)).sum
    simp only [List.length_append, anchorAddresses, List.length_ofFn, List.map_cons, List.sum_cons]
    exact congrArg ((P label).count+·) hr.1
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
      change (if bits j then 1 else 0)<r.variables+2
      split_ifs <;> omega
    · exact hr.2 v hv

variable {K : Type*} [CommSemiring K]
variable (g : (i : Fin s) → Signature K (P i).count)

def weight (r : Raw s) (a : ℕ → Bool) : K := W.weight P g r.labels (fun k => a (r.addresses.getD k 0))

def anchor {n : ℕ} (u v : Bool) (x : Fin n → Bool) : ℕ → Bool
  | 0 => u
  | 1 => v
  | k+2 => R.read x k

def fixed (r : Raw s) (u v : Bool) : K := ∑x : Fin r.variables → Bool, weight P g r (anchor u v x)

theorem value_eq (r : Raw s) : value P g r=∑x : Fin r.variables → Bool, weight P g r (R.read x) := rfl

theorem read_cons {n : ℕ} (u : Bool) (x : Fin n → Bool) (k : ℕ) :
    R.read (Fin.cons u x) k = if k=0 then u else R.read x (k-1) := by
  cases k with
  | zero => simp [R.read]
  | succ k =>
    by_cases hk : k<n
    · simp [R.read, hk, show k+1<n+1 by omega]
      rfl
    · simp [R.read, hk, show ¬k+1<n+1 by omega]

theorem read_anchor {n : ℕ} (u v : Bool) (x : Fin n → Bool) :
    R.read (Fin.cons u (Fin.cons v x))=anchor u v x := by
  funext k
  cases k with
  | zero => simp [read_cons, anchor]
  | succ k => cases k with
    | zero => simp [read_cons, anchor]
    | succ k => simp [read_cons, anchor]

theorem sum_cons {n : ℕ} (H : (Fin (n+1) → Bool) → K) :
    (∑x,H x)=∑b : Bool,∑x : Fin n → Bool,H (Fin.cons b x) := by
  let : Fintype (Bool × (Fin n → Bool)) := @instFintypeProd _ _ Bool.fintype inferInstance
  rw [←(Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem free_value (r : Raw s) : value P g (free r)=
    fixed P g r false false+fixed P g r false true+
      fixed P g r true false+fixed P g r true true := by
  rw [value_eq]
  change (∑x : Fin (r.variables+2) → Bool, weight P g r (R.read x))=_
  rw [sum_cons]
  simp_rw [sum_cons, read_anchor]
  simp only [Fintype.sum_bool]
  ac_rfl

theorem merge_weight (r : Raw s) (b : Bool) (x : Fin r.variables → Bool) :
    weight P g (merge r) (R.read (Fin.cons b x))=weight P g r (anchor b b x) := by
  unfold weight W.weight
  dsimp only [merge]
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext j
  rw [List.getD_map (f := fun k : ℕ => k-1) (l := r.addresses) (d := 0)]
  generalize r.addresses.getD _ 0=k
  cases k with
  | zero => simp [read_cons, anchor]
  | succ k => cases k with
    | zero => simp [read_cons, anchor]
    | succ k => simp [read_cons, anchor]

theorem merge_value (r : Raw s) :
    value P g (merge r)=fixed P g r false false+fixed P g r true true := by
  rw [value_eq]
  change (∑x : Fin (r.variables+1) → Bool, weight P g (merge r) (R.read x))=_
  rw [sum_cons]
  simp_rw [merge_weight]
  rw [Fintype.sum_bool]
  exact add_comm _ _

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPinRaw
