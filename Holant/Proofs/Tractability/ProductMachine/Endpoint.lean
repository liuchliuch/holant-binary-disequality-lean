import Holant.Complexity.FixedGadgetSubstitution.Compiler.Template
import Holant.Complexity.GraphPreprocessing.FiniteRecode
import Holant.Complexity.FixedFieldMachines.PrimitiveCost


namespace Holant.LocalDrafts.Tractability.ProductMachine.Endpoint

open Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing

def number (p : RawEndpoint) : ℕ := 2 * p.1 + p.2.toNat

def unnumber (n : ℕ) : RawEndpoint := (n / 2, decide (n % 2 = 1))

theorem unnumber_number (p : RawEndpoint) : unnumber (number p) = p := by
  rcases p with ⟨e, b⟩
  cases b <;> simp [number, unnumber, Nat.add_div, Nat.add_mod]

theorem number_unnumber (n : ℕ) : number (unnumber n) = n := by
  have hm := Nat.mod_lt n (by decide : 0 < 2)
  have hd := Nat.mod_add_div n 2
  by_cases h : n % 2 = 1
  · simp [number, unnumber, h]; omega
  · have hz : n % 2 = 0 := by omega
    simp [number, unnumber, h]; omega

def typed (E : ℕ) (p : Fin E × Bool) : Fin (2 * E) :=
  ⟨number (p.1.val, p.2), by cases p.2 <;> simp [number] <;> omega⟩

def equivalence (E : ℕ) : (Fin E × Bool) ≃ Fin (2 * E) where
  toFun := typed E
  invFun i := (⟨i.val / 2, by omega⟩, decide (i.val % 2 = 1))
  left_inv p := by
    have hraw : unnumber (number (p.1.val, p.2)) = (p.1.val, p.2) :=
      unnumber_number (p.1.val, p.2)
    have hfst : number (p.1.val, p.2) / 2 = p.1.val :=
      congrArg (fun q : RawEndpoint => q.1) hraw
    have hsnd : decide (number (p.1.val, p.2) % 2 = 1) = p.2 :=
      congrArg (fun q : RawEndpoint => q.2) hraw
    have htyped :
        ((⟨number (p.1.val, p.2) / 2, by
          have hp := (typed E p).isLt
          change number (p.1.val, p.2) < 2 * E at hp
          omega⟩ : Fin E), decide (number (p.1.val, p.2) % 2 = 1)) = p :=
      Prod.ext (Fin.ext hfst) hsnd
    exact htyped
  right_inv i := by
    apply Fin.ext
    exact number_unnumber i.val

@[simp] theorem typed_val (E : ℕ) (p : Fin E × Bool) :
    (typed E p).val = 2 * p.1.val + p.2.toNat := rfl

noncomputable def bitComputes : Computes encodingBoolBool encodingNatBool Bool.toNat :=
  FiniteRecode.computes encodingBoolBool encodingNatBool Bool.toNat 1 (fun b => by cases b <;> decide)

noncomputable def edgeComputes : Computes RawClosedNetwork.endpointEncoding encodingNatBool Prod.fst :=
  recode (Wiring.firstComputes encodingNatBool encodingBoolBool) id
    (fun _ => rfl) (fun _ => rfl)

noncomputable def endBitComputes : Computes RawClosedNetwork.endpointEncoding encodingBoolBool Prod.snd :=
  recode (Wiring.secondComputes encodingNatBool encodingBoolBool) id
    (fun _ => rfl) (fun _ => rfl)

noncomputable def computes : Computes RawClosedNetwork.endpointEncoding encodingNatBool number :=
  congrComputes
    ((pairComputes
      ((pairComputes edgeComputes edgeComputes).andThen
        FixedGadgetSubstitution.Compiler.addComputes)
      (endBitComputes.andThen bitComputes)).andThen
        FixedGadgetSubstitution.Compiler.addComputes)
    (fun p => by simp [number, two_mul])

theorem inFP : InFP RawClosedNetwork.endpointEncoding encodingNatBool number := computes.inFP

/-- This counts actual primitive instructions, not unit-cost natural addition. -/
theorem primitive_bound (p : RawEndpoint) :
    primitiveCost computes.machine (computes.outputs p).steps
      (some (Turing.initList computes.machine.computer (RawClosedNetwork.endpointEncoding.encode p))) ≤
        (primitivePolynomial computes).eval (RawClosedNetwork.endpointEncoding.encode p).length :=
  computes_primitive_cost computes p

end Holant.LocalDrafts.Tractability.ProductMachine.Endpoint
