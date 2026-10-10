import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.MuxMachine

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-!
# Physical finite-control truth-table compilation

Ported reference proof. See the task validation reports.

Only fixed verifier alphabets are parameters of the machines in this file.
Encoded environments contain runtime register indices; their values are read,
added and serialized by actual subprograms. Do not instantiate this construction
with a capacity-dependent address type to claim a uniform machine.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.FiniteMachine


open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler OutputMachine
open scoped Classical

variable {I O P J : Type}

def referenceEncoding (I : Type) [Fintype I] : Encoding (I → ℕ) Bool where
  encode refs := (framedListEncoding encodingNatBool).encode (Environment.pack (fixedEnum I) refs)
  decode bits := do
    let env ← (framedListEncoding encodingNatBool).decode bits
    pure (Environment.lookup (fixedEnum I) env)
  decode_encode refs := by
    rw [(framedListEncoding encodingNatBool).decode_encode]
    change some (Environment.lookup (fixedEnum I) (Environment.pack (fixedEnum I) refs)) = some refs
    congr 1
    funext i
    exact Environment.lookup_pack _ refs i (mem_fixedEnum i)

def resultEncoding (O : Type) [Fintype O] := pairEncoding Frame.wordEncoding (referenceEncoding O)
def result {O : Type} (r : Rows.Result O) : List Bool × (O → ℕ) := (rowBytes r.1, r.2)

def getComputes [Fintype I] (i : I) : Computes (referenceEncoding I) encodingNatBool (fun env => env i) :=
  recode (getDComputes encodingNatBool ((fixedEnum I).idxOf i) 0)
    (Environment.pack (fixedEnum I)) (fun _ => rfl)
    (fun env => congrArg encodingNatBool.encode (Environment.lookup_pack _ env i (mem_fixedEnum i)))

def shiftComputes [Fintype I] (g : ℕ) :
    Computes (referenceEncoding I) (referenceEncoding I) (Rows.shift g) := by
  let provider (i : I) := (pairComputes (getComputes i)
    (constantComputes (referenceEncoding I) encodingNatBool g)).andThen addComputes
  exact recode (fixedListComputes (referenceEncoding I) encodingNatBool
    (fun env i => env i + g) provider (fixedEnum I)) id (fun _ => rfl) (fun _ => rfl)

theorem listOr_length (xs : List I) (env : I → ℕ) :
    (Rows.listOr xs env).1.length = 3 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp [Rows.listOr, Rows.seq, Rows.parallel, Rows.route, Rows.or, Rows.not,
      Rows.nand, Rows.shift, ih, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem listOr_output (xs : List I) (env : I → ℕ) : (Rows.listOr xs env).2 () = 0 := by
  cases xs <;> rfl

theorem listOr_cons (a : I) (xs : List I) (env : I → ℕ) :
    (Rows.listOr (a :: xs) env).1 = (Rows.listOr xs env).1 ++
      [(2, (env a + (3 * xs.length + 1), env a + (3 * xs.length + 1))),
        (2, (1, 1)), (2, (1, 0))] := by
  simp [Rows.listOr, Rows.seq, Rows.parallel, Rows.route, Rows.or, Rows.not,
    Rows.nand, Rows.shift, listOr_length, listOr_output, Nat.add_assoc]

def listOrComputes [Fintype I] : (xs : List I) →
    Computes (referenceEncoding I) Frame.wordEncoding (fun env => rowBytes (Rows.listOr xs env).1)
  | [] => constantComputes _ _ (rowBytes [(0, (0, 0))])
  | a :: xs => by
    let r := (pairComputes (getComputes a)
      (constantComputes (referenceEncoding I) encodingNatBool (3 * xs.length + 1))).andThen addComputes
    let first := (pairComputes r r).andThen RuntimeRows.nandEntryComputes
    let rest := constantComputes (referenceEncoding I) Frame.wordEncoding
      (rowBytes [(2, (1, 1)), (2, (1, 0))])
    refine congrComputes (joinComputes (listOrComputes xs) (joinComputes first rest)) ?_
    intro env
    rw [listOr_cons, rowBytes_append]
    simp [rowBytes, entries, entry, List.append_assoc]

/-- A fixed list of blocks may have different fixed gate counts. Each following
provider is fed a physically shifted input vector, not a host-function update. -/
def gatherComputes [Fintype I] (p : J → Rows.Run I Unit) (cost : J → ℕ)
    (hlen : ∀ j env, (p j env).1.length = cost j)
    (w : ∀ j, Computes (referenceEncoding I) Frame.wordEncoding (fun env => rowBytes (p j env).1)) :
    (xs : List J) → Computes (referenceEncoding I) Frame.wordEncoding
      (fun env => rowBytes (Rows.gather p xs env).1)
  | [] => constantComputes _ _ []
  | j :: xs => by
    refine congrComputes (joinComputes (w j)
      ((shiftComputes (cost j)).andThen (gatherComputes p cost hlen w xs))) ?_
    intro env
    simp [Rows.gather, Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route, hlen, rowBytes_append]

def tabulateComputes [Fintype I] [Fintype O] (xs : List O) (covers : ∀ o, o ∈ xs)
    (p : O → Rows.Run I Unit) (cost : O → ℕ)
    (hlen : ∀ o env, (p o env).1.length = cost o) (hz : ∀ o env, (p o env).2 () = 0)
    (w : ∀ o, Computes (referenceEncoding I) Frame.wordEncoding (fun env => rowBytes (p o env).1)) :
    Computes (referenceEncoding I) (resultEncoding O) (fun env => result (Rows.tabulate xs covers p env)) := by
  let output := fun o => ((xs.drop (xs.idxOf o + 1)).map cost).sum
  refine congrComputes (pairComputes (gatherComputes p cost hlen w xs)
    (constantComputes (referenceEncoding I) (referenceEncoding O) output)) ?_
  intro env
  apply Prod.ext
  · simp [result, Rows.tabulate, Rows.renameOutput, Rows.seq, Rows.route]
  · funext o
    exact (Rows.tabulate_output xs covers p cost hlen hz env o).symm

def tableComputes [Fintype I] [Fintype O] (f : I → O) :
    Computes (referenceEncoding I) (resultEncoding O) (fun env => result (Rows.table f env)) :=
  tabulateComputes (fixedEnum O) mem_fixedEnum
    (fun o => Rows.listOr ((fixedEnum I).filter (fun i => decide (f i = o))))
    (fun o => 3 * ((fixedEnum I).filter (fun i => decide (f i = o))).length + 1)
    (fun _ env => listOr_length _ env) (fun _ env => listOr_output _ env) (fun _ => listOrComputes _)

def routeComputes [Fintype I] [Fintype O] (f : O → I) :
    Computes (referenceEncoding I) (resultEncoding O) (fun env => result (Rows.route f env)) := by
  let outputs : Computes (referenceEncoding I) (referenceEncoding O) (fun env o => env (f o)) :=
    recode (fixedListComputes (referenceEncoding I) encodingNatBool (fun env o => env (f o))
      (fun o => getComputes (f o)) (fixedEnum O)) id (fun _ => rfl) (fun _ => rfl)
  exact pairComputes (constantComputes (referenceEncoding I) Frame.wordEncoding []) outputs

/-- Real sequential composition for finite-control blocks. Recomputing a fixed
subprogram through pair wiring is allowed and its runtime is fully charged by
the existing composition theorem; it is not identified with the gate count. -/
def seqComputes [Fintype I] [Fintype O] [Fintype P] (p : Rows.Run I O) (q : Rows.Run O P)
    (wp : Computes (referenceEncoding I) (resultEncoding O) (fun env => result (p env)))
    (wq : Computes (referenceEncoding O) (resultEncoding P) (fun env => result (q env))) :
    Computes (referenceEncoding I) (resultEncoding P) (fun env => result (Rows.seq p q env)) := by
  let firstRows := wp.andThen (Wiring.firstComputes Frame.wordEncoding (referenceEncoding O))
  let next := (wp.andThen (Wiring.secondComputes Frame.wordEncoding (referenceEncoding O))).andThen wq
  let secondRows := next.andThen (Wiring.firstComputes Frame.wordEncoding (referenceEncoding P))
  let output := next.andThen (Wiring.secondComputes Frame.wordEncoding (referenceEncoding P))
  exact congrComputes (pairComputes (joinComputes firstRows secondRows) output)
    (fun env => by simp [result, Rows.seq, rowBytes_append])

def andRowsComputes [Fintype I] (a b : I) :
    Computes (referenceEncoding I) Frame.wordEncoding (fun env => rowBytes (Rows.and a b env).1) := by
  let first := (pairComputes (getComputes a) (getComputes b)).andThen RuntimeRows.nandEntryComputes
  refine congrComputes (joinComputes first
    (constantComputes (referenceEncoding I) Frame.wordEncoding (entry Circuit.rowEncoding (2, (0, 0))))) ?_
  intro env
  simp [Rows.and, Rows.seq, Rows.not, Rows.nand, rowBytes, entries, entry, List.append_assoc]

def crossComputes [Fintype I] [Fintype O] :
    Computes (referenceEncoding (I ⊕ O)) (resultEncoding (I × O))
      (fun env => result (Rows.cross (A := I) (B := O) env)) := by
  let w := tabulateComputes (I := I ⊕ O) (O := I × O) (fixedEnum (I × O)) mem_fixedEnum
    (fun ab : I × O => Rows.and (I := I ⊕ O) (.inl ab.1) (.inr ab.2)) (fun _ => 2)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun ab : I × O => andRowsComputes (I := I ⊕ O) (.inl ab.1) (.inr ab.2))
  refine congrComputes w ?_
  intro env
  unfold Rows.cross
  congr 2
  exact Subsingleton.elim _ _

def table₂Computes [Fintype I] [Fintype O] [Fintype P] (f : I → O → P) :
    Computes (referenceEncoding (I ⊕ O)) (resultEncoding P) (fun env => result (Rows.table₂ f env)) :=
  seqComputes _ _ crossComputes (tableComputes (fun ab : I × O => f ab.1 ab.2))

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.FiniteMachine
