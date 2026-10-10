import Holant.Complexity.UniversalPairReduction.OrderedGadget

/-! Original literal input records for at most one Delta. The promise does not
change the encoding: validation checks the occurrence bound on the original
vertex stream, and forgetting the promise is a one-step identity machine. -/
namespace Holant.Complexity.UniversalPairReduction
open Computability BinaryCompose FixedGadgetSubstitution FixedFieldMachines

variable (s : ℕ) (arity : ℕ → ℕ)

abbrev Input := { r : RawClosedNetwork //
  r.WellFormed (s+1) 1 (extendedArity s arity) ∧ occurrences s r ≤ 1 }

def inputEncoding : Encoding (Input s arity) Bool where
  encode r := RawClosedNetwork.encoding.encode r.val
  decode bits := (RawClosedNetwork.encoding.decode bits).bind fun r =>
    if h : r.WellFormed (s+1) 1 (extendedArity s arity) ∧ occurrences s r ≤ 1
      then some ⟨r,h⟩ else none
  decode_encode r := by simp [r.property]

def forget (r : Input s arity) :
    { r : RawClosedNetwork // r.WellFormed (s+1) 1 (extendedArity s arity) } :=
  ⟨r.val,r.property.1⟩

noncomputable def forgetComputes : Computes (inputEncoding s arity)
    (RawClosedNetwork.validatedEncoding (s+1) 1 (extendedArity s arity)) (forget s arity) :=
  recode (identityComputes (inputEncoding s arity)) id (fun _ => rfl) (fun _ => rfl)

/-- No fresh representation hides or compresses the promise. -/
theorem inputEncoding_literal (r : Input s arity) :
    (inputEncoding s arity).encode r = RawClosedNetwork.encoding.encode r.val := rfl

theorem absent_label {r : RawClosedNetwork} (h : occurrences s r = 0)
    (row : RawVertex) (hr : row ∈ r.vertices) : row.1 ≠ s := by
  intro he
  have hm : row ∈ r.vertices.filter (fun row => row.1 == s) := by simp [hr,he]
  have hz : r.vertices.filter (fun row => row.1 == s) = [] := List.length_eq_zero_iff.mp h
  rw [hz] at hm
  exact List.not_mem_nil hm

/-- The zero-occurrence branch preserves the full raw record and all original
nullary vertices, loops and parallel edges. -/
theorem zero_wellFormed (r : Input s arity) (h : occurrences s r.val = 0) :
    r.val.WellFormed s 1 arity := by
  refine ⟨?_,r.property.1.2.1,r.property.1.2.2⟩
  intro v
  have hv := r.property.1.1 v
  have hn := absent_label s h (r.val.vertices.get v) (List.get_mem _ _)
  have hs : (r.val.vertices.get v).1 < s := by omega
  exact ⟨hs,hv.2.trans (if_pos hs)⟩

abbrev ZeroInput := { r : Input s arity // occurrences s r.val = 0 }

def zeroEncoding : Encoding (ZeroInput s arity) Bool where
  encode r := (inputEncoding s arity).encode r.val
  decode bits := ((inputEncoding s arity).decode bits).bind fun r =>
    if h : occurrences s r.val = 0 then some ⟨r,h⟩ else none
  decode_encode r := by simp [r.property]

def zeroQuery (r : ZeroInput s arity) :
    { r : RawClosedNetwork // r.WellFormed s 1 arity } :=
  ⟨r.val.val,zero_wellFormed s arity r.val r.property⟩

noncomputable def zeroQueryComputes : Computes (zeroEncoding s arity)
    (RawClosedNetwork.validatedEncoding s 1 arity) (zeroQuery s arity) :=
  recode (identityComputes (zeroEncoding s arity)) id (fun _ => rfl) (fun _ => rfl)

end Holant.Complexity.UniversalPairReduction
