import Holant.Proofs.Algorithms.OneQueryControl
import Holant.Complexity.OracleReductionCompose


namespace Holant.LocalDrafts.MainChain
open Computability Holant.Complexity Holant.Complexity.BinaryCompose

variable {α β γ δ ε ζ : Type}
    {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool}
    {ee : Encoding ε Bool} {ef : Encoding ζ Bool}
    {pre : α → γ} {post : δ → β} {g : γ → δ}

/-- Every actual query is the verified compiler output, with its derived bound. -/
noncomputable def controlledOneQuery (a : Computes ea ec pre)
    (b : Computes ed eb post) (size : PolynomialOutputBound ec ed g) :
    LengthControlledOracleReduction ea eb ec ed (post ∘ g ∘ pre) g where
  reduction := OracleOneQuery.reduction a b size
  targetOutput := size
  queryBound := a.outputBound.bound
  safeQuery oracle _ x t c hr hq := by
    have hc := OneQueryControl.query_configuration a.machine b.machine oracle
      (ea.encode x) (ec.encode (pre x)) (a.outputs x).steps t c
      (a.outputs x).evals_in_steps hr hq
    subst c
    refine ⟨pre x, ?_, ?_⟩
    · rw [OracleOneQuery.left_halt]
      exact wordTape_at _ _
    · rw [OracleOneQuery.left_halt]
      simpa only [StackProtocol.cfg, OracleOneQuery.reduction, OracleOneQuery.machine, wordTape_at] using
        a.outputBound.length_le x

/-- The equality is a semantic interface for a separately implemented compiler;
the query-safety proof above does not take it as an assumption. -/
noncomputable def controlledOneQueryOfEq (a : Computes ea ec pre)
    (b : Computes ed eb post) (size : PolynomialOutputBound ec ed g)
    (f : α → β) (heq : ∀ x, f x = post (g (pre x))) :
    LengthControlledOracleReduction ea eb ec ed f g := by
  have hf : f = post ∘ g ∘ pre := funext heq
  subst f
  exact controlledOneQuery a b size

theorem controlledOneQueryOfEq_queryBound (a : Computes ea ec pre)
    (b : Computes ed eb post) (size : PolynomialOutputBound ec ed g)
    (f : α → β) (heq : ∀ x, f x = post (g (pre x))) :
    (controlledOneQueryOfEq a b size f heq).queryBound = a.outputBound.bound := by
  have hf : f = post ∘ g ∘ pre := funext heq
  subst f
  rfl

/-- Real finite-machine composition, available for any verified target reducer. -/
noncomputable def oneQueryThen (a : Computes ea ec pre)
    (b : Computes ed eb post) (size : PolynomialOutputBound ec ed g)
    (f : α → β) (heq : ∀ x, f x = post (g (pre x)))
    {h : ε → ζ} (r : PolyTimeOracleReduction ec ed ee ef g h) :
    PolyTimeOracleReduction ea eb ee ef f h :=
  (controlledOneQueryOfEq a b size f heq).compose r

end Holant.LocalDrafts.MainChain
