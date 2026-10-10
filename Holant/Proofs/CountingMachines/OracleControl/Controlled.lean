import Holant.Proofs.CountingMachines.OracleControl.OneQuery
import Holant.Complexity.OracleSpace

/-! Actual-run query validity for the existing finite one-query program. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
open Turing Computability Holant.Complexity BinaryCompose OracleOneQuery

variable {α β γ δ : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool}
  {pre : α → γ} {post : δ → β} {g : γ → δ}

noncomputable def controlled (a : Computes ea ec pre) (b : Computes ed eb post)
    (size : PolynomialOutputBound ec ed g) :
    LengthControlledOracleReduction ea eb ec ed (post ∘ g ∘ pre) g where
  reduction := OracleOneQuery.reduction a b size
  targetOutput := size
  queryBound := a.outputBound.bound
  safeQuery oracle _ x t c hr hq := by
    have hc := query_configuration a.machine b.machine oracle (ea.encode x)
      (ec.encode (pre x)) (a.outputs x).steps t c (a.outputs x).evals_in_steps hr hq
    subst c
    refine ⟨pre x, ?_, ?_⟩
    · rw [left_halt]
      simp [StackProtocol.cfg, wordTape, OracleOneQuery.reduction, machine]
    · rw [left_halt]
      simpa [StackProtocol.cfg, wordTape, OracleOneQuery.reduction, machine] using a.outputBound.length_le x

noncomputable def controlledOfEq (a : Computes ea ec pre) (b : Computes ed eb post)
    (size : PolynomialOutputBound ec ed g) (f : α → β)
    (heq : ∀ x, f x = post (g (pre x))) :
    LengthControlledOracleReduction ea eb ec ed f g := by
  have hfun : f = post ∘ g ∘ pre := funext heq
  subst f
  exact controlled a b size

end Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
