import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.PlanRows

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Equality of the physical initial plan's actual records to the existing row
emitter. This concerns gate order and operands, not just Boolean denotation.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.InitialExact

open Holant.LocalDrafts.CountingHardness

open Turing Holant.Complexity BitLayout InitialPlan
open scoped Classical

variable (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]
variable (e : tm.Γ tm.k₀ ≃ Bool ⊕ Bool) (p : Input)

def coordinate : Address tm p.2.2 → Item
  | .inl l => constant (oneHot (some tm.main) l)
  | .inr (.inl s) => constant (oneHot tm.initialState s)
  | .inr (.inr ⟨k, i, a⟩) => cell tm e p k i.val a

theorem plan_map : plan tm e p = (addresses tm p.2.2).map (coordinate tm e p) := plan_order tm e p

theorem input_records (i : Fin (p.2.2 + 1)) (a : Option (tm.Γ tm.k₀)) (g : ℕ) :
    PlanRows.records (inputCell tm e p i.val a) g =
      (InitialRows.inputBit tm p.2.2 e p.1 p.2.1 i a (Rows.shift g Fin.val)).1 := by
  by_cases hi : i.val < p.1.length
  · have ht : (Initial.tokens p.1 p.2.1)[i.val]? = some (.inl p.1[i.val]) := by
      rw [Initial.tokens, List.getElem?_append_left (by simpa using hi)]
      simp [List.getElem?_eq_getElem hi]
    rw [input_region tm e p i.val hi, InitialRows.inputBit, ht]
    rfl
  · by_cases hw : i.val < p.1.length + p.2.1
    · have hj : i.val - p.1.length < p.2.1 := by omega
      have ht : (Initial.tokens p.1 p.2.1)[i.val]? =
          some (.inr (⟨i.val - p.1.length, hj⟩ : Fin p.2.1)) := by
        rw [Initial.tokens, List.getElem?_append_right (by simp; omega)]
        simp [List.getElem?_eq_getElem, hj]
      rw [witness_region tm e p i.val (by omega) hw, InitialRows.inputBit, ht]
      simp [PlanRows.records, witness, MuxMachine.records, InitialRows.boolMap,
        Rows.seq, Rows.parallel, Rows.route, Rows.constant, Rows.mux, Rows.nand,
        Rows.not, Rows.shift, Nat.add_assoc]
    · have ht : (Initial.tokens p.1 p.2.1)[i.val]? = none :=
        List.getElem?_eq_none (by simp [Initial.tokens]; omega)
      rw [padding_region tm e p i.val (by omega), InitialRows.inputBit, ht]
      rfl

theorem coordinate_records (a : Address tm p.2.2) (g : ℕ) :
    PlanRows.records (coordinate tm e p a) g =
      (InitialRows.bit tm p.2.2 e p.1 p.2.1 a (Rows.shift g Fin.val)).1 := by
  rcases a with l | s | ⟨k, i, b⟩
  · rfl
  · rfl
  · by_cases hk : k = tm.k₀
    · subst k
      simpa [coordinate, cell, InitialRows.bit] using input_records tm e p i b g
    · simp [coordinate, cell, InitialRows.bit, hk, PlanRows.records, constant, Rows.constant]

theorem bit_length_independent (a : Address tm p.2.2) (u v : Fin p.2.1 → ℕ) :
    (InitialRows.bit tm p.2.2 e p.1 p.2.1 a u).1.length =
      (InitialRows.bit tm p.2.2 e p.1 p.2.1 a v).1.length := by
  rcases a with l | s | ⟨k, i, b⟩
  · rfl
  · rfl
  · by_cases hk : k = tm.k₀
    · subst k
      simp only [InitialRows.bit, dif_pos rfl, InitialRows.inputBit]
      cases ht : (Initial.tokens p.1 p.2.1)[i.val]? with
      | none => rfl
      | some t =>
        cases t with
        | inl b => rfl
        | inr j =>
          simp [InitialRows.boolMap, Rows.seq, Rows.parallel, Rows.route, Rows.constant,
            Rows.mux, Rows.nand, Rows.not]
    · simp [InitialRows.bit, hk, Rows.constant]

theorem bit_length (a : Address tm p.2.2) (env : Fin p.2.1 → ℕ) :
    (InitialRows.bit tm p.2.2 e p.1 p.2.1 a env).1.length = cost (coordinate tm e p a) := by
  rw [bit_length_independent tm e p a env (Rows.shift 0 Fin.val), ← coordinate_records]
  exact PlanRows.records_length _ _

theorem bit_output (a : Address tm p.2.2) (env : Fin p.2.1 → ℕ) :
    (InitialRows.bit tm p.2.2 e p.1 p.2.1 a env).2 () = 0 := by
  rcases a with l | s | ⟨k, i, b⟩
  · rfl
  · rfl
  · by_cases hk : k = tm.k₀
    · subst k
      simp only [InitialRows.bit, dif_pos rfl, InitialRows.inputBit]
      cases ht : (Initial.tokens p.1 p.2.1)[i.val]? with
      | none => rfl
      | some t => cases t <;> rfl
    · simp [InitialRows.bit, hk, Rows.constant]

theorem gather_variable {I J : Type} (blocks : J → Rows.Run I Unit) (cost : J → ℕ)
    (hlen : ∀ j env, (blocks j env).1.length = cost j) (xs : List J) (env : I → ℕ) :
    (Rows.gather blocks xs env).1 = (List.ofFn (fun i : Fin xs.length =>
      (blocks (xs.get i) (Rows.shift (((xs.take i.val).map cost).sum) env)).1)).flatten := by
  induction xs generalizing env with
  | nil => rfl
  | cons j xs ih =>
    simp only [Rows.gather, Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
      List.append_nil, hlen, List.ofFn_succ, List.flatten_cons, Fin.val_zero,
      Fin.val_succ, List.get_cons_zero, List.get_cons_succ', List.take_zero,
      List.map_nil, List.sum_nil, List.take_succ_cons, List.map_cons, List.sum_cons]
    rw [ih]
    congr 1
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    congr 2
    funext a
    simp [Rows.shift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem planRows_ofFn (xs : List Item) : PlanRows.rows xs =
    (List.ofFn (fun i : Fin xs.length =>
      PlanRows.records (xs.get i) (((xs.take i.val).map cost).sum))).flatten := by
  rw [PlanRows.rows, ← Layout.finRange_flatMap]
  simp only [List.ofFn_eq_map, List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  rw [PlanRows.prefix_eq_take _ _ (Nat.le_of_lt i.isLt), List.getD_eq_getElem _ _ i.isLt]
  rfl

theorem initial_rows : PlanRows.rows (plan tm e p) =
    (InitialRows.initial tm p.2.2 e p.1 p.2.1 Fin.val).1 := by
  rw [planRows_ofFn, plan_map]
  change _ = (Rows.gather (InitialRows.bit tm p.2.2 e p.1 p.2.1)
    (addresses tm p.2.2) Fin.val).1 ++ []
  rw [List.append_nil, gather_variable _ (fun a => cost (coordinate tm e p a)) (bit_length tm e p)]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.get_eq_getElem, List.getElem_map,
      ← List.map_take, List.map_map, Function.comp_def]
    exact coordinate_records tm e p _ _

theorem initial_references : PlanRows.references (plan tm e p) =
    (addresses tm p.2.2).map (InitialRows.initial tm p.2.2 e p.1 p.2.1 Fin.val).2 := by
  letI : BEq (Address tm p.2.2) := instBEqOfDecidableEq
  rw [PlanRows.references, plan_map]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hii : i < (addresses tm p.2.2).length := by simpa using hj
    simp only [List.getElem_map, List.getElem_range]
    rw [PlanRows.suffix_eq_drop _ _ (by simpa using hii)]
    have hout := Rows.tabulate_output (addresses tm p.2.2) (mem_addresses tm p.2.2)
      (InitialRows.bit tm p.2.2 e p.1 p.2.1) (fun a => cost (coordinate tm e p a))
      (bit_length tm e p) (bit_output tm e p) Fin.val ((addresses tm p.2.2)[i])
    rw [(Layout.addresses_nodup tm p.2.2).idxOf_getElem i hii] at hout
    simpa [InitialRows.initial, ← List.map_drop, List.map_map, Function.comp_def] using hout.symm

theorem initial_result : PlanRows.result (plan tm e p) =
    (OutputMachine.rowBytes (InitialRows.initial tm p.2.2 e p.1 p.2.1 Fin.val).1,
      (addresses tm p.2.2).map (InitialRows.initial tm p.2.2 e p.1 p.2.1 Fin.val).2) := by
  apply Prod.ext
  · exact congrArg OutputMachine.rowBytes (initial_rows tm e p)
  · exact initial_references tm e p

variable {α : Type} {ea : Computability.Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)
local instance : ∀ k, Fintype (w.verifier.tm.Γ k) := w.verifier.finiteAlphabets

theorem original_rows (a : α) :
    PlanRows.rows (plan w.verifier.tm w.verifier.inputAlphabet
      (ea.encode a, VerifierRun.witnessLength w a, capacity w (ea.encode a))) =
      (InitialRows.initialResult w (ea.encode a)).1 :=
  initial_rows w.verifier.tm w.verifier.inputAlphabet _

/-- Original input only. Both gate bytes and every live initial reference are
generated by the physical plan program and identified with the old emitter. -/
def computes : Holant.Complexity.BinaryCompose.Computes ea PlanRows.resultEncoding
    (fun a => (OutputMachine.rowBytes (InitialRows.initialResult w (ea.encode a)).1,
      (addresses w.verifier.tm (capacity w (ea.encode a))).map
        (InitialRows.initialResult w (ea.encode a)).2)) :=
  Holant.Complexity.FixedFieldMachines.congrComputes (PlanRows.originalComputes w)
    (fun a => initial_result w.verifier.tm w.verifier.inputAlphabet _)

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.InitialExact
