import Holant.Proofs.BinaryInterpolation.EncodedBatch
import Holant.Proofs.BinaryInterpolation.PostprocessBounds


namespace Holant.LocalDrafts.BinaryInterpolation.OracleAnswerBounds
open Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.Complexity.FixedGadgetSubstitution Holant.Complexity.FixedFieldMachines
open Holant.Algebraic Holant.OneHot
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

variable {K D : Type} [CommSemiring K]

/-- Pad one unit per edge: every assignment contributes a product of degree
V+2E, and there are at most 2^(V+2E) assignments. No assignment enumeration is
executed by the reduction; this is a size certificate for the oracle answer. -/
theorem network_bound (base : D → K) (unit : D) (hunit : base unit = 1)
    {n : ℕ} (N : Network K n)
    (vl : (v : Fin N.shape.vertices) → Signature D (N.shape.arity v))
    (el : Fin N.shape.edges → Bool → Bool → D)
    (hv : ∀ v x, N.vertex v x = base (vl v x))
    (he : ∀ e a b, N.edge e a b = base (el e a b)) (x : Fin n → Bool) :
    ArithmeticSize.Bound base ((N.shape.vertices+N.shape.edges)+N.shape.edges) (N.denote x) := by
  classical
  let en := (Fintype.equivFin ((Fin N.shape.edges × Bool) → Bool)).symm
  refine ⟨Fintype.card ((Fin N.shape.edges × Bool) → Bool),
    (fun t => Fin.addCases
      (Fin.addCases (fun v => vl v (N.shape.assignment x (en t) v))
        (fun e => el e (en t (e,false)) (en t (e,true))))
      (fun _ : Fin N.shape.edges => unit)), ?_, ?_⟩
  · have hcard : Fintype.card ((Fin N.shape.edges × Bool) → Bool) =
        2^(2*N.shape.edges) := by simp [Nat.mul_comm]
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · simp only [Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right,
      hunit, Finset.prod_const_one, mul_one]
    rw [en.sum_comp (fun z =>
      (∏ v, base (vl v (N.shape.assignment x z v))) *
        ∏ e, base (el e (z (e,false)) (z (e,true))))]
    simp only [Network.denote, hv, he]

end

noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s b arity) (gamma rho : K)

abbrev Index := Fin 4 ⊕ ExactSignatureTables.CoefficientIndex s b arity

def coordinates : Index (s:=s) (b:=b) (arity:=arity) → Fin n → ℚ
  | .inl a => F.decode.symm (WeightFormulas.coefficients gamma rho a)
  | .inr a => T.coefficient a

theorem decode_unit : F.decode (coordinates F T gamma rho (.inl 3)) = 1 := by
  simp [coordinates, WeightFormulas.coefficients]

theorem literal_bound (a : Fin 4) :
    ArithmeticSize.Bound (fun d => F.decode (coordinates F T gamma rho d)) 1
      (WeightFormulas.coefficients gamma rho a) := by
  simpa [coordinates] using
    (ArithmeticSize.Bound.coefficient (coeff:=fun d => F.decode (coordinates F T gamma rho d)) (.inl a))

theorem answer_bound (q : ExactSignatureTables.Input s b arity) :
    ArithmeticSize.Bound (fun d => F.decode (coordinates F T gamma rho d))
      ((q.val.vertices.length+q.val.edges.length)+q.val.edges.length) (T.evaluate F q) := by
  apply network_bound _ (.inl 3) (decode_unit F T gamma rho)
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
    ArithmeticSize.Bound (fun d => F.decode (coordinates F T gamma rho d))
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
  apply (answer_bound F T gamma rho q).mono (.inl 3) (decode_unit F T gamma rho)
  simp only [answerBudgetPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat]
  change q.val.vertices.length+q.val.edges.length ≤
    ((RawClosedNetwork.validatedEncoding s b arity).encode q).length at hsize
  omega

/-- The budget supplied to the actual postprocessor is obtained from the
actual compiled query list and the original input bytes. -/
theorem sample_answers_bound
    (r : EncodedBatch.Source (s:=s) (b:=b) arity g)
    (i : Fin (occurrences s r.val+1)) :
    ArithmeticSize.Bound (fun d => F.decode (coordinates F T gamma rho d))
      ((answerBudgetPolynomial g hg hbinary edge).eval
        ((EncodedBatch.sourceEncoding (s:=s) (b:=b) arity g).encode r).length)
      (T.evaluate F (Chains.Compiler.OriginalFamily.value arity g hg hbinary edge ⟨r,i⟩)) := by
  apply emitted_answer_bound F T gamma rho g hg hbinary edge r
  unfold EncodedBatch.queries Chains.Compiler.Batch.samples
  exact List.mem_map.mpr ⟨i, by simp, rfl⟩

end
end Holant.LocalDrafts.BinaryInterpolation.OracleAnswerBounds
