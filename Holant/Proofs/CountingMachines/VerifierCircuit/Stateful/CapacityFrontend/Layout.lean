import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.ListAccess
import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CanonicalMachine

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Uniform layout traversal and heterogeneous offsets. Only the verifier's finite
alphabets are construction-time lists. Every cell loop consumes runtime C+1.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Layout


open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler BitLayout
open scoped Classical

variable {A B : Type}

def rank {A : Type} [Fintype A] (a : A) : ℕ := (fixedEnum A).idxOf a

theorem rank_lt {A : Type} [Fintype A] (a : A) : rank a < Fintype.card A := by
  simpa [rank] using List.idxOf_lt_length_iff.mpr (mem_fixedEnum a)

theorem split_at (xs : List A) (i : ℕ) (hi : i < xs.length) :
    xs = xs.take i ++ xs[i] :: xs.drop (i + 1) := by
  rw [List.getElem_cons_drop, List.take_append_drop]

theorem read_block (xs : List A) (f : A → List B) (i : ℕ) (hi : i < xs.length)
    (j : ℕ) (hj : j < (f xs[i]).length) (d : B) :
    (xs.flatMap f).getD (((xs.take i).flatMap f).length + j) d = (f xs[i]).getD j d := by
  conv_lhs => arg 1; rw [split_at xs i hi]
  rw [List.flatMap_append, List.flatMap_cons]
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
  rw [Nat.add_sub_cancel_left, List.getD_append _ _ _ _ hj]

theorem read_fixed (e : A → B) [Fintype A] (a : A) (d : B) :
    ((fixedEnum A).map e).getD (rank a) d = e a := by
  have hi := rank_lt a
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [rank]

theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

theorem finRange_flatMap (n : ℕ) (f : ℕ → List B) :
    (List.finRange n).flatMap (fun i => f i.val) = (List.range n).flatMap f := by
  rw [← finRange_values n, List.flatMap_map]

variable (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]

def alphabetWidth (k : tm.K) : ℕ := Fintype.card (Option (tm.Γ k))
def beforeWidth (k : tm.K) : ℕ :=
  (((fixedEnum tm.K).take (rank k)).map (alphabetWidth tm)).sum
def stackStart (C : ℕ) (k : tm.K) : ℕ := controlWidth tm + (C + 1) * beforeWidth tm k
def cellIndex (C : ℕ) (k : tm.K) (i : ℕ) (a : Option (tm.Γ k)) : ℕ :=
  stackStart tm C k + i * alphabetWidth tm k + rank a
def stateIndex (s : tm.σ) : ℕ := Fintype.card (Option tm.Λ) + rank s

def cellBlock (C : ℕ) (k : tm.K) (env : Address tm C → B) : List B :=
  (List.finRange (C + 1)).flatMap (fun i =>
      (fixedEnum (Option (tm.Γ k))).map (fun a => env (cellAddr tm C k i a)))

def values (C : ℕ) (label : Option tm.Λ → B) (state : tm.σ → B)
    (cell : (k : tm.K) → ℕ → Option (tm.Γ k) → B) : List B :=
  (fixedEnum (Option tm.Λ)).map label ++ (fixedEnum tm.σ).map state ++
    (fixedEnum tm.K).flatMap (fun k => (List.range (C + 1)).flatMap (fun i =>
      (fixedEnum (Option (tm.Γ k))).map (cell k i)))

theorem values_pack (C : ℕ) (label : Option tm.Λ → B) (state : tm.σ → B)
    (cell : (k : tm.K) → ℕ → Option (tm.Γ k) → B) :
    values tm C label state cell = (addresses tm C).map (fun a => match a with
      | .inl l => label l
      | .inr (.inl s) => state s
      | .inr (.inr ⟨k, i, b⟩) => cell k i.val b) := by
  simp only [values, addresses, List.map_append, List.map_map, List.map_flatMap,
    Function.comp_def, labelAddr, stateAddr, cellAddr]
  simp only [← finRange_values (C + 1), List.flatMap_map]

theorem cellBlock_length (C : ℕ) (k : tm.K) (env : Address tm C → B) :
    (cellBlock tm C k env).length = (C + 1) * alphabetWidth tm k := by
  simp [cellBlock, List.length_flatMap, alphabetWidth]

theorem blocks_length (C : ℕ) (ks : List tm.K) (env : Address tm C → B) :
    (ks.flatMap (fun k => cellBlock tm C k env)).length =
      (C + 1) * (ks.map (alphabetWidth tm)).sum := by
  induction ks with
  | nil => simp
  | cons k ks ih => simp [ih, cellBlock_length, Nat.mul_add]

theorem pack_order (C : ℕ) (env : Address tm C → B) :
    (addresses tm C).map env =
      (fixedEnum (Option tm.Λ)).map (fun l => env (labelAddr tm C l)) ++
      (fixedEnum tm.σ).map (fun s => env (stateAddr tm C s)) ++
      (fixedEnum tm.K).flatMap (fun k => cellBlock tm C k env) := by
  simp [addresses, cellBlock, List.map_flatMap, List.map_map, Function.comp_def]

theorem fixedEnum_nodup (A : Type) [Fintype A] : (fixedEnum A).Nodup :=
  List.nodup_ofFn.mpr (Fintype.equivFin A).symm.injective

theorem addresses_nodup (C : ℕ) : (addresses tm C).Nodup := by
  let cells (k : tm.K) := (List.finRange (C + 1)).flatMap (fun i =>
    (fixedEnum (Option (tm.Γ k))).map (cellAddr tm C k i))
  have hc (k : tm.K) : (cells k).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨?_, (List.nodup_finRange (C + 1)).imp ?_⟩
    · intro i _
      apply (fixedEnum_nodup (Option (tm.Γ k))).map
      intro a b hab
      simpa [cellAddr] using hab
    · intro i j hij z hz hz'
      rcases List.mem_map.mp hz with ⟨a, _, rfl⟩
      rcases List.mem_map.mp hz' with ⟨b, _, he⟩
      have hp := congrArg (fun x : Address tm C => match x with
        | .inr (.inr ⟨_, pos, _⟩) => pos.val
        | _ => 0) he
      exact hij (Fin.ext hp.symm)
  have hs : ((fixedEnum tm.K).flatMap cells).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun k _ => hc k, (fixedEnum_nodup tm.K).imp ?_⟩
    intro k j hkj z hz hz'
    rcases List.mem_flatMap.mp hz with ⟨i, _, hi⟩
    rcases List.mem_map.mp hi with ⟨a, _, rfl⟩
    rcases List.mem_flatMap.mp hz' with ⟨i', _, hi'⟩
    rcases List.mem_map.mp hi' with ⟨b, _, he⟩
    have hp := congrArg (fun x : Address tm C => match x with
      | .inr (.inr ⟨key, _, _⟩) => some key
      | _ => none) he
    exact hkj (Option.some.inj hp).symm
  have hl := (fixedEnum_nodup (Option tm.Λ)).map (f := labelAddr tm C)
    (fun a b h => by simpa [labelAddr] using h)
  have ht := (fixedEnum_nodup tm.σ).map (f := stateAddr tm C)
    (fun a b h => by simpa [stateAddr] using h)
  unfold addresses
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨hl, ht, ?_⟩, hs, ?_⟩
  · intro x hx y hy
    rcases List.mem_map.mp hx with ⟨l, _, rfl⟩
    rcases List.mem_map.mp hy with ⟨s, _, rfl⟩
    simp [labelAddr, stateAddr]
  · intro x hx y hy
    rcases List.mem_flatMap.mp hy with ⟨k, _, hi⟩
    rcases List.mem_flatMap.mp hi with ⟨i, _, ha⟩
    rcases List.mem_map.mp ha with ⟨a, _, rfl⟩
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_map.mp hx with ⟨l, _, rfl⟩
      simp [labelAddr, cellAddr]
    · rcases List.mem_map.mp hx with ⟨s, _, rfl⟩
      simp [stateAddr, cellAddr]

theorem read_label (C : ℕ) (env : Address tm C → B) (l : Option tm.Λ) (d : B) :
    ((addresses tm C).map env).getD (rank l) d = env (labelAddr tm C l) := by
  rw [pack_order, List.getD_append _ _ _ _ (by
    simp only [List.length_append, List.length_map, fixedEnum_length]
    have h := rank_lt l
    omega)]
  rw [List.getD_append _ _ _ _ (by simpa using rank_lt l)]
  exact read_fixed _ l d

theorem read_state (C : ℕ) (env : Address tm C → B) (s : tm.σ) (d : B) :
    ((addresses tm C).map env).getD (stateIndex tm s) d = env (stateAddr tm C s) := by
  rw [pack_order, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp [stateIndex])]
  simp only [List.length_map, fixedEnum_length, stateIndex, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa using rank_lt s)]
  exact read_fixed _ s d

theorem read_cell (C : ℕ) (env : Address tm C → B) (k : tm.K)
    (i : Fin (C + 1)) (a : Option (tm.Γ k)) (d : B) :
    ((addresses tm C).map env).getD (cellIndex tm C k i.val a) d = env (cellAddr tm C k i a) := by
  have ha := rank_lt a
  have hk : rank k < (fixedEnum tm.K).length := by simpa using rank_lt k
  have hget : (fixedEnum tm.K)[rank k] = k := by
    have h := read_fixed (fun x : tm.K => x) k k
    simpa only [List.map_id', List.getD_eq_getElem _ _ hk] using h
  change rank a < alphabetWidth tm k at ha
  have inner : i.val * alphabetWidth tm k + rank a < (cellBlock tm C k env).length := by
    rw [cellBlock_length]
    have h := Nat.mul_le_mul_right (alphabetWidth tm k) (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at h
    omega
  rw [pack_order, List.getD_append_right _ _ _ _ (by simp [cellIndex, stackStart, controlWidth]; omega)]
  simp only [List.length_append, List.length_map, fixedEnum_length]
  have ho : cellIndex tm C k i.val a -
      (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) =
        (((fixedEnum tm.K).take (rank k)).flatMap (fun j => cellBlock tm C j env)).length +
          (i.val * alphabetWidth tm k + rank a) := by
    rw [blocks_length]
    simp [cellIndex, stackStart, controlWidth, beforeWidth, Nat.add_assoc]
    omega
  rw [ho, read_block _ _ _ hk _ (by simpa [hget] using inner), hget]
  have hp : (((List.finRange (C + 1)).take i.val).flatMap (fun j =>
      (fixedEnum (Option (tm.Γ k))).map (fun b => env (cellAddr tm C k j b)))).length =
        i.val * alphabetWidth tm k := by
    simp [List.length_flatMap, alphabetWidth, Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  unfold cellBlock
  rw [← hp, read_block _ _ _ (by simpa using i.isLt) _ (by simpa [alphabetWidth] using ha)]
  simpa using read_fixed (fun b => env (cellAddr tm C k i b)) a d

def widthComputes : Computes Unary.encoding Unary.encoding
    (fun C => controlWidth tm + (C + 1) * cellWidth tm) :=
  congrComputes ((pairComputes (constantComputes Unary.encoding Unary.encoding (controlWidth tm))
    (Unary.successorComputes.andThen (Unary.scaleComputes (cellWidth tm)))).andThen Unary.addComputes)
    (fun C => by simp [Nat.mul_comm])

def stackStartComputes (k : tm.K) : Computes Unary.encoding Unary.encoding (fun C => stackStart tm C k) :=
  congrComputes ((pairComputes (constantComputes Unary.encoding Unary.encoding (controlWidth tm))
    (Unary.successorComputes.andThen (Unary.scaleComputes (beforeWidth tm k)))).andThen Unary.addComputes)
    (fun C => by simp [stackStart, Nat.mul_comm])

def cellIndexComputes (k : tm.K) (a : Option (tm.Γ k)) :
    Computes (pairEncoding Unary.encoding Unary.encoding) Unary.encoding
      (fun p => cellIndex tm p.1 k p.2 a) := by
  let start := (Wiring.firstComputes Unary.encoding Unary.encoding).andThen (stackStartComputes tm k)
  let cell := (Wiring.secondComputes Unary.encoding Unary.encoding).andThen
    (Unary.scaleComputes (alphabetWidth tm k))
  exact congrComputes ((pairComputes ((pairComputes start cell).andThen Unary.addComputes)
    (constantComputes _ Unary.encoding (rank a))).andThen Unary.addComputes)
      (fun _ => by simp [cellIndex, Nat.mul_comm])

/-- Physical nested enumeration in exactly the old address order. The variable
cell count belongs to the encoded input; fixed alphabets only choose providers. -/
def tabulateComputes (ea : Encoding A Bool) (eb : Encoding B Bool) (cap : A → ℕ)
    (wc : Computes ea Unary.encoding cap)
    (label : A → Option tm.Λ → B) (state : A → tm.σ → B)
    (cell : A → (k : tm.K) → ℕ → Option (tm.Γ k) → B)
    (wl : ∀ l, Computes ea eb (fun x => label x l))
    (ws : ∀ s, Computes ea eb (fun x => state x s))
    (wk : ∀ k a, Computes (pairEncoding ea Unary.encoding) eb (fun x => cell x.1 k x.2 a)) :
    Computes ea (framedListEncoding eb) (fun x =>
      (fixedEnum (Option tm.Λ)).map (label x) ++ (fixedEnum tm.σ).map (state x) ++
      (fixedEnum tm.K).flatMap (fun k => (List.range (cap x + 1)).flatMap (fun i =>
        (fixedEnum (Option (tm.Γ k))).map (cell x k i)))) := by
  let ls := fixedListComputes ea eb label wl (fixedEnum (Option tm.Λ))
  let ss := fixedListComputes ea eb state ws (fixedEnum tm.σ)
  let ks := fixedConcatComputes ea (fun x k =>
      (List.range (cap x + 1)).flatMap (fun i =>
        (fixedEnum (Option (tm.Γ k))).flatMap (fun a => entry eb (cell x k i a))))
    (fun k => Support.WordLoops.rangeWordsComputes ea (fun x => cap x + 1)
      (wc.andThen Unary.successorComputes) _
      (fixedConcatComputes (pairEncoding ea Unary.encoding) _
        (fun a => (wk k a).andThen (entryComputes eb)) (fixedEnum (Option (tm.Γ k)))))
    (fixedEnum tm.K)
  let «prefix» := (pairComputes ls ss).andThen (ListAccess.appendComputes eb)
  refine recode (joinComputes («prefix».andThen (entriesComputes eb))
    (joinComputes ks (constantComputes ea Frame.wordEncoding [false]))) id (fun _ => rfl) ?_
  intro x
  have h := entries_append_encode eb
    ((fixedEnum (Option tm.Λ)).map (label x) ++ (fixedEnum tm.σ).map (state x) ++
      (fixedEnum tm.K).flatMap (fun k => (List.range (cap x + 1)).flatMap (fun i =>
        (fixedEnum (Option (tm.Γ k))).map (cell x k i)))) []
  simpa [entries, List.flatMap_append, List.flatMap_assoc, List.flatMap_map,
    Function.comp_def, Frame.wordEncoding, framedListEncoding, framedListEncode,
    List.append_assoc] using h

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Layout
