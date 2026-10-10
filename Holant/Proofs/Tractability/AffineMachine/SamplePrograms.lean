import Holant.Proofs.Tractability.AffineMachine.AccessPrograms
import Holant.Proofs.Tractability.AffineMachine.RawBlocks


namespace Holant.LocalDrafts.Tractability.AffineMachine.SamplePrograms

set_option backward.isDefEq.respectTransparency false
open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open ProductMachine

abbrev Mask := Bool × (ℕ × (Bool × ℕ))
def maskEncoding := pairEncoding encodingBoolBool
  (pairEncoding encodingNatBool (pairEncoding encodingBoolBool encodingNatBool))
def origin : Mask := (false, 0, false, 0)
def single (i : ℕ) : Mask := (true, i, false, 0)
def pair (i j : ℕ) : Mask := (true, i, true, j)
def «at» (m : Mask) (i : ℕ) : Bool :=
  Bool.xor (m.1 && decide (m.2.1 = i)) (m.2.2.1 && decide (m.2.2.2 = i))

noncomputable def leftFlag := Wiring.firstComputes encodingBoolBool
  (pairEncoding encodingNatBool (pairEncoding encodingBoolBool encodingNatBool))
noncomputable def tail := Wiring.secondComputes encodingBoolBool
  (pairEncoding encodingNatBool (pairEncoding encodingBoolBool encodingNatBool))
noncomputable def left := tail.andThen (Wiring.firstComputes encodingNatBool (pairEncoding encodingBoolBool encodingNatBool))
noncomputable def rightPart := tail.andThen (Wiring.secondComputes encodingNatBool (pairEncoding encodingBoolBool encodingNatBool))
noncomputable def rightFlag := rightPart.andThen (Wiring.firstComputes encodingBoolBool encodingNatBool)
noncomputable def right := rightPart.andThen (Wiring.secondComputes encodingBoolBool encodingNatBool)

noncomputable def atComputes : Computes (pairEncoding maskEncoding encodingNatBool) encodingBoolBool
    (fun x => «at» x.1 x.2) := by
  let mask := Wiring.firstComputes maskEncoding encodingNatBool
  let index := Wiring.secondComputes maskEncoding encodingNatBool
  exact AccessPrograms.bool Bool.xor
    (AccessPrograms.bool Bool.and (mask.andThen leftFlag)
      (AccessPrograms.eqNat (mask.andThen left) index))
    (AccessPrograms.bool Bool.and (mask.andThen rightFlag)
      (AccessPrograms.eqNat (mask.andThen right) index))

noncomputable def singleComputes : Computes UnaryBinary.unaryEncoding maskEncoding single :=
  pairComputes (constantComputes _ _ true) (pairComputes UnaryBinary.computes
    (pairComputes (constantComputes _ _ false) (constantComputes _ _ 0)))

noncomputable def pairComputes : Computes (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
    maskEncoding (fun x => pair x.1 x.2) :=
  FixedFieldMachines.pairComputes (constantComputes _ _ true)
    (FixedFieldMachines.pairComputes ((Wiring.firstComputes _ _).andThen UnaryBinary.computes)
      (FixedFieldMachines.pairComputes (constantComputes _ _ true)
        ((Wiring.secondComputes _ _).andThen UnaryBinary.computes)))

def parity (m : Mask) (indices : List ℕ) : Bool := ResidueCells.parity (indices.map («at» m))

noncomputable def parityComputes : Computes (pairEncoding maskEncoding (framedListEncoding encodingNatBool))
    encodingBoolBool (fun x => parity x.1 x.2) :=
  (mapListComputes maskEncoding encodingNatBool encodingBoolBool «at» atComputes).andThen ResidueCells.parityComputes

/-- Total finite-case decoder for coefficients emitted from the fixed templates.
The bound proving agreement with the original coefficient is below. -/
def small4 (n : ℕ) : ZMod 4 := if n = 0 then 0 else if n = 1 then 1 else if n = 2 then 2 else 3

noncomputable def small4Computes : Computes encodingNatBool ResidueCells.encoding4 small4 := by
  let eq (k : ℕ) := AccessPrograms.eqNat (identityComputes encodingNatBool)
    (constantComputes encodingNatBool encodingNatBool k)
  exact congrComputes (ifComputes (eq 0) (constantComputes _ ResidueCells.encoding4 0)
    (ifComputes (eq 1) (constantComputes _ ResidueCells.encoding4 1)
      (ifComputes (eq 2) (constantComputes _ ResidueCells.encoding4 2) (constantComputes _ ResidueCells.encoding4 3))))
    (fun n => by simp [small4])

theorem small4_val (q : ZMod 4) : small4 q.val = q := by fin_cases q <;> rfl

def record (m : Mask) (r : Templates.Record) : ZMod 4 :=
  if r.1 = 0 then small4 r.2.1 else
    if r.1 = 1 then small4 r.2.2.1 * FiniteCore.bit4 («at» m r.2.1) else
      2 * small4 r.2.2.2.1 * FiniteCore.bit4 («at» m r.2.1) * FiniteCore.bit4 («at» m r.2.2.1)

def recordEncoding := pairEncoding maskEncoding Templates.recordEncoding

noncomputable def recordComputes : Computes recordEncoding ResidueCells.encoding4 (fun x => record x.1 x.2) := by
  let mask := Wiring.firstComputes maskEncoding Templates.recordEncoding
  let row := Wiring.secondComputes maskEncoding Templates.recordEncoding
  let get (i : Fin 5) := row.andThen (Rewrite.getComputes i)
  let coeff (i : Fin 5) := (get i).andThen small4Computes
  let bit (i : Fin 5) := ((FixedFieldMachines.pairComputes mask (get i)).andThen atComputes).andThen ResidueCells.bool4
  let tag (i : ℕ) := AccessPrograms.eqNat (get 0) (constantComputes recordEncoding encodingNatBool i)
  let mixed := AccessPrograms.residue (· * ·)
    (AccessPrograms.residue (· * ·)
      (AccessPrograms.residue (· * ·) (constantComputes recordEncoding ResidueCells.encoding4 2) (coeff 3))
      (bit 1)) (bit 2)
  exact congrComputes (ifComputes (tag 0) (coeff 1)
    (ifComputes (tag 1) (AccessPrograms.residue (· * ·) (coeff 2) (bit 1)) mixed))
      (fun x => by
        simp only [Function.comp_apply, Rewrite.get, record]
        simp only [decide_eq_true_eq]
        rfl)

def phase (m : Mask) (rs : List Templates.Record) : ZMod 4 := (rs.map (record m)).sum

noncomputable def phaseComputes : Computes (pairEncoding maskEncoding RawBlocks.phaseEncoding)
    ResidueCells.encoding4 (fun x => phase x.1 x.2) :=
  (mapListComputes maskEncoding Templates.recordEncoding ResidueCells.encoding4 record recordComputes).andThen
    ResidueCells.sum4

theorem record_template {n : ℕ} (Q : QuadraticPhase n) (ports : List RawEndpoint)
    (m : Mask) (f : Templates.LocalFactor) (hf : f ∈ RawBlocks.phaseTemplate Q) :
    record m (Templates.place ports f) = RawBlocks.recordValue («at» m) (Templates.place ports f) := by
  simp only [RawBlocks.phaseTemplate, List.mem_append, List.mem_cons, List.mem_nil_iff,
    or_false, List.mem_map, List.mem_flatMap, List.mem_filterMap] at hf
  rcases hf with (rfl | ⟨j, _, rfl⟩) | ⟨j, _, k, _, hk⟩
  · simp [record, Templates.place, RawBlocks.recordValue, small4_val]
  · simp [record, Templates.place, RawBlocks.recordValue, small4_val, FiniteCore.bit4, bitValue]
  · split at hk
    · simp only [Option.some.injEq] at hk
      subst f
      cases h : decide (Q.mixed j k = 2) <;>
        simp [record, Templates.place, RawBlocks.recordValue, h, small4, FiniteCore.bit4, bitValue]
    · simp at hk

theorem phase_template {n : ℕ} (Q : QuadraticPhase n) (ports : List RawEndpoint) (m : Mask) :
    phase m (RawBlocks.phaseRecords Q ports) =
      Q.eval (fun j => «at» m (ProductMachine.Endpoint.number (ports.getD j.val (0, false)))) := by
  rw [← RawBlocks.phaseRecords_exact Q ports («at» m)]
  unfold phase RawBlocks.phaseRecords
  congr 1
  apply List.map_congr_left
  intro r hr
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hr
  exact record_template Q ports m f hf

end Holant.LocalDrafts.Tractability.AffineMachine.SamplePrograms
