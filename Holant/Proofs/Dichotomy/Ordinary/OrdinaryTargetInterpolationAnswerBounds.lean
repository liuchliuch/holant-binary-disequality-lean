import Holant.Proofs.BinaryInterpolation.OracleAnswerBounds
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationPostprocess

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationAnswerBounds
open Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.Complexity.FixedGadgetSubstitution Holant.Complexity.FixedFieldMachines
open Holant.Algebraic Holant.OneHot
open Holant.LocalDrafts.BinaryInterpolation
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s b arity) (gamma rho target : K)

abbrev Index := Fin 5 ⊕ ExactSignatureTables.CoefficientIndex s b arity

def coordinates : Index (s:=s) (b:=b) (arity:=arity) → Fin n → ℚ
  | .inl a => F.decode.symm (![gamma,rho,-1,target,1] a)
  | .inr a => T.coefficient a

theorem decode_unit : F.decode (coordinates F T gamma rho target (.inl 4)) = 1 := by
  simp [coordinates]

theorem literal_bound (a : Fin 4) :
    ArithmeticSize.Bound (fun d=>F.decode (coordinates F T gamma rho target d)) 1
      (OrdinaryNegativeBinaryUnsignedInterpolationFormulas.coefficients gamma rho target a) := by
  have h := ArithmeticSize.Bound.coefficient
    (coeff:=fun d=>F.decode (coordinates F T gamma rho target d)) (.inl (Fin.castAdd 1 a))
  fin_cases a <;> simpa [coordinates,OrdinaryNegativeBinaryUnsignedInterpolationFormulas.coefficients] using h

theorem answer_bound (q : ExactSignatureTables.Input s b arity) :
    ArithmeticSize.Bound (fun d => F.decode (coordinates F T gamma rho target d))
      ((q.val.vertices.length+q.val.edges.length)+q.val.edges.length) (T.evaluate F q) := by
  apply Holant.LocalDrafts.BinaryInterpolation.OracleAnswerBounds.network_bound _ (.inl 4) (decode_unit F T gamma rho target)
    (q.val.realize q.property (fun i x => F.decode (T.vertex i x))
      (fun i a b => F.decode (T.edge i a b)))
    (fun v x => .inr (.inl ⟨q.val.signatureLabel q.property v,x⟩))
    (fun e a b => .inr (.inr (q.val.edgeLabel q.property e,a,b)))
    (fun _ _ => rfl) (fun _ _ _ => rfl) Fin.elim0

variable (g : Template) (hg : g.WellFormed s b arity) (hbinary : g.boundary = 2) (edge : Fin b)

def answerBudgetPolynomial : Polynomial ℕ :=
  2*(EncodedBatch.queriesComputes arity g hg hbinary edge).outputBound.bound

theorem emitted_answer_bound
    (r : EncodedBatch.Source (s:=s) (b:=b) arity g)
    (q : ExactSignatureTables.Input s b arity)
    (hq : q ∈ EncodedBatch.queries arity g hg hbinary edge r) :
    ArithmeticSize.Bound (fun d => F.decode (coordinates F T gamma rho target d))
      ((answerBudgetPolynomial g hg hbinary edge).eval
        ((EncodedBatch.sourceEncoding (s:=s) (b:=b) arity g).encode r).length)
      (T.evaluate F q) := by
  have hmember := OracleBatch.member_length_le
    ((EncodedBatch.queries arity g hg hbinary edge r).map
      (RawClosedNetwork.validatedEncoding s b arity).encode)
    ((RawClosedNetwork.validatedEncoding s b arity).encode q)
    (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hlist := (EncodedBatch.queriesComputes arity g hg hbinary edge).outputBound.length_le r
  rw [OracleBatch.list_encode] at hlist
  change (OracleBatch.listWord ((EncodedBatch.queries arity g hg hbinary edge r).map
    (RawClosedNetwork.validatedEncoding s b arity).encode)).length ≤ _ at hlist
  have hsize := q.val.counts_le_encoded_length
  apply (answer_bound F T gamma rho target q).mono (.inl 4) (decode_unit F T gamma rho target)
  simp only [answerBudgetPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat]
  change q.val.vertices.length+q.val.edges.length ≤
    ((RawClosedNetwork.validatedEncoding s b arity).encode q).length at hsize
  omega

/-- The budget supplied to the actual postprocessor is obtained from the
actual compiled query list and the original input bytes. -/
theorem sample_answers_bound
    (r : EncodedBatch.Source (s:=s) (b:=b) arity g)
    (i : Fin (occurrences s r.val+1)) :
    ArithmeticSize.Bound (fun d => F.decode (coordinates F T gamma rho target d))
      ((answerBudgetPolynomial g hg hbinary edge).eval
        ((EncodedBatch.sourceEncoding (s:=s) (b:=b) arity g).encode r).length)
      (T.evaluate F (Chains.Compiler.OriginalFamily.value arity g hg hbinary edge ⟨r,i⟩)) := by
  apply emitted_answer_bound F T gamma rho target g hg hbinary edge r
  unfold EncodedBatch.queries Chains.Compiler.Batch.samples
  exact List.mem_map.mpr ⟨i, by simp, rfl⟩

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationAnswerBounds
