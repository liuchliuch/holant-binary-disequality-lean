import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.Rows

set_option backward.isDefEq.respectTransparency false

/-!
# Serialized live register contexts and parallel save/restore

Ported reference proof. See the task validation reports.

The machine data are lists of natural register indices. Mathematical functions
are only related to those lists by `pack`/`lookup_pack`, never stored in TM2
finite control. Save/restore uses real framed pair wiring programs.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Environment


open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient

abbrev Env := List ℕ
abbrev encoding := RuntimeRows.environmentEncoding

def pack {I : Type} (layout : List I) (refs : I → ℕ) : Env := layout.map refs

def lookup {I : Type} [DecidableEq I] (layout : List I) (env : Env) (i : I) : ℕ :=
  env.getD (layout.idxOf i) 0

theorem lookup_pack {I : Type} [DecidableEq I] (layout : List I) (refs : I → ℕ)
    (i : I) (hi : i ∈ layout) : lookup layout (pack layout refs) i = refs i := by
  have hidx := List.idxOf_lt_length_iff.mpr hi
  simp only [lookup, pack]
  rw [List.getD_eq_getElem _ _ (by simpa using hidx)]
  simp only [List.getElem_map, List.getElem_idxOf hidx]

@[simp] theorem pack_length {I : Type} (layout : List I) (refs : I → ℕ) :
    (pack layout refs).length = layout.length := by simp [pack]

def shift (g : ℕ) (env : Env) : Env := env.map (fun r => r + g)

theorem shift_pack {I : Type} (g : ℕ) (layout : List I) (refs : I → ℕ) :
    shift g (pack layout refs) = pack layout (Rows.shift g refs) := by
  simp [shift, pack, Rows.shift, List.map_map, Function.comp_def]

theorem shift_shift (g h : ℕ) (env : Env) : shift h (shift g env) = shift (g + h) env := by
  simp [shift, List.map_map, Function.comp_def, Nat.add_assoc]

def Bounded (n : ℕ) (env : Env) : Prop := ∀ r ∈ env, r < n

theorem pack_bounded {I : Type} (layout : List I) {n : ℕ} (refs : I → Fin n) :
    Bounded n (pack layout (fun i => (refs i).val)) := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  exact (refs i).isLt

theorem shift_bounded {n : ℕ} {env : Env} (h : Bounded n env) (g : ℕ) :
    Bounded (n + g) (shift g env) := by
  intro r hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  exact Nat.add_lt_add_right (h s hs) g

theorem pack_sum {I J : Type} (left : List I) (right : List J) (f : I → ℕ) (g : J → ℕ) :
    pack (left.map Sum.inl ++ right.map Sum.inr) (Sum.elim f g) = pack left f ++ pack right g := by
  simp [pack, List.map_map, Function.comp_def]

def shiftComputes : Computes (pairEncoding encodingNatBool encoding) encoding
    (fun x => shift x.1 x.2) :=
  congrComputes RuntimeRows.shiftEnvironmentComputes (fun x => by
    simp [shift, Nat.add_comm])

/-- A valid index is represented by the existing physical unary selector.
Its length is therefore charged, including the zero index. -/
def lookupComputes : Computes (ParentRowSelect.inputEncoding encodingNatBool) encodingNatBool
    (fun x => x.1.get x.2) := ParentRowSelect.computes encodingNatBool

def contextInputEncoding := pairEncoding encoding encoding
def savedLeftEncoding := pairEncoding contextInputEncoding encoding
def rightCallEncoding := pairEncoding contextInputEncoding encoding

/-- (context, input) ↦ ((context, original input), input). Both copies are
physically emitted by the standard pair program before the left call. -/
def saveOriginalComputes : Computes contextInputEncoding savedLeftEncoding
    (fun x : Env × Env => (x, x.2)) :=
  pairComputes (identityComputes contextInputEncoding) (Wiring.secondComputes encoding encoding)

/-- After the left call, ((context, original input), left output) is rewired to
((context, left output), original input) for the right call. Shifts have already
been applied by that call's row-count update. -/
def enterRightComputes : Computes savedLeftEncoding rightCallEncoding
    (fun x : (Env × Env) × Env => ((x.1.1, x.2), x.1.2)) := by
  let saved := Wiring.firstComputes contextInputEncoding encoding
  let left := Wiring.secondComputes contextInputEncoding encoding
  exact pairComputes
    (pairComputes (saved.andThen (Wiring.firstComputes encoding encoding)) left)
    (saved.andThen (Wiring.secondComputes encoding encoding))

/-- The right call leaves ((context, left output), right output). The public
result is context plus the ordered pair of both retained output lists. -/
def restoreComputes : Computes rightCallEncoding (pairEncoding encoding contextInputEncoding)
    (fun x : (Env × Env) × Env => (x.1.1, (x.1.2, x.2))) := by
  let saved := Wiring.firstComputes contextInputEncoding encoding
  let right := Wiring.secondComputes contextInputEncoding encoding
  exact pairComputes (saved.andThen (Wiring.firstComputes encoding encoding))
    (pairComputes (saved.andThen (Wiring.secondComputes encoding encoding)) right)

theorem parallel_pack {I O P : Type} (outputs : List O) (outputs' : List P)
    (p : Rows.Run I O) (q : Rows.Run I P) (input : I → ℕ) :
    pack (outputs.map Sum.inl ++ outputs'.map Sum.inr) (Rows.parallel p q input).2 =
      shift (q (Rows.shift (p input).1.length input)).1.length (pack outputs (p input).2) ++
        pack outputs' (q (Rows.shift (p input).1.length input)).2 := by
  rw [Rows.parallel, pack_sum, shift_pack]

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Environment
