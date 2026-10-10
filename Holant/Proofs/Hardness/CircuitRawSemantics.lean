import Holant.Proofs.Counting.RawGraphMachine.Frontend
import Holant.Proofs.Counting.NetworkSemantics


/-! Unchanged circuit-only semantic core, extracted to avoid importing the legacy verifier compiler. -/
noncomputable section
namespace Holant.LocalDrafts.CountingHardness.RawGraphMachine
open Computability Holant.Complexity BinaryCompose

theorem value_nat (c : CircuitInstance) :
    ((RawCompiler.validated c).val.realize (RawCompiler.validated c).property
      (GateAlphabet.signatures (K := ℕ)) (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0 = c.value :=
  NetworkSemantics.compile_denote_nat c

theorem value_complex (c : CircuitInstance) :
    ((RawCompiler.validated c).val.realize (RawCompiler.validated c).property
      (GateAlphabet.signatures (K := ℂ)) (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0 = (c.value : ℂ) :=
  NetworkSemantics.compile_denote_complex c

end Holant.LocalDrafts.CountingHardness.RawGraphMachine
