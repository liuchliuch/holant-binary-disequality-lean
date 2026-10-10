import Holant.Proofs.Hardness.PositiveDynamicProgrammeRoots

/-! Polynomial common-denominator/field-bit heights for the actual stage/root
formula programme. The alphabet is fixed original-field data, never the
input-dependent eigenmodes treated as constants. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicProgrammeRootBounds
open Holant Holant.Algebraic Holant.Complexity Holant.OneHot
open BinaryInterpolation
namespace P
export PositiveDynamicProgrammeFormulas
  (Labels Formula coefficients lam mu nu root desired eval_lam eval_mu eval_nu
    eval_root eval_desired size_lam size_mu size_nu size_root_le size_desired_le)
end P
namespace R
export PositiveDynamicProgrammeRoots (stageLength lam mu nu root roots)
end R
variable {K I : Type} [Field K] (base : I→K) (a b c : K)
variable (embed : P.Labels→I) (he : ∀i,base (embed i)=P.coefficients a b c i)

include he in
theorem formula_bound (p : P.Formula) :
    ArithmeticSize.Bound base p.size (p.eval (P.coefficients a b c)) := by
  obtain ⟨L,f,hL,hv⟩ := (p.structural_bound (P.coefficients a b c) 5 rfl).1
  refine ⟨L,fun t i=>embed (f t i),hL,?_⟩
  simpa only [he] using hv

def parameterBudget (C : ℕ) : Polynomial ℕ := 6*Polynomial.C C*(Polynomial.X+1)+10

@[simp] theorem parameterBudget_eval (C m : ℕ) :
    (parameterBudget C).eval m=6*(C*(m+1))+10 := by
  simp only [parameterBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_one]
  ring

include he in
/-- All three stage coefficients are calculated from the same fixed literal
alphabet. Their sum-product heights grow linearly with the original count. -/
theorem parameters_bound (C m : ℕ) :
    ArithmeticSize.Bound base ((parameterBudget C).eval m) (R.lam C a b m) ∧
    ArithmeticSize.Bound base ((parameterBudget C).eval m) (R.mu C a b c m) ∧
    ArithmeticSize.Bound base ((parameterBudget C).eval m) (R.nu C a b c m) := by
  have hl := formula_bound base a b c embed he (P.lam (R.stageLength C m))
  have hu := formula_bound base a b c embed he (P.mu (R.stageLength C m))
  have hv := formula_bound base a b c embed he (P.nu (R.stageLength C m))
  rw [P.eval_lam] at hl
  rw [P.eval_mu] at hu
  rw [P.eval_nu] at hv
  refine ⟨hl.mono (embed 5) (he 5) ?_,hu.mono (embed 5) (he 5) ?_,
    hv.mono (embed 5) (he 5) ?_⟩ <;>
    simp only [P.size_lam,P.size_mu,P.size_nu,parameterBudget_eval,R.stageLength] <;> omega

def budget (C : ℕ) : Polynomial ℕ := Polynomial.X*(6*Polynomial.C C*(Polynomial.X+1)+10)+5
@[simp] theorem budget_eval (C m : ℕ) : (budget C).eval m=m*(6*(C*(m+1))+10)+5 := by
  simp only [budget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_one]
  ring

include he in
theorem root_bound (C m : ℕ) {ij : ℕ×ℕ} (hij : ij.1+ij.2≤m) :
    ArithmeticSize.Bound base ((budget C).eval m) (R.root C a b c (m,ij)) := by
  have h := formula_bound base a b c embed he (P.root (R.stageLength C m) m ij)
  rw [P.eval_root] at h
  exact h.mono (embed 5) (he 5) (by
    rw [budget_eval]
    exact P.size_root_le (R.stageLength C m) m ij hij)

include he in
theorem roots_bound (C m : ℕ) :
    ∀r∈R.roots C a b c m,ArithmeticSize.Bound base ((budget C).eval m) r := by
  intro r hr
  obtain ⟨ij,hij,rfl⟩ := List.mem_map.mp hr
  exact root_bound base a b c embed he C m (ThreeModeAnnihilator.mem_rootIndices.mp hij).1

include he in
theorem desired_bound (C m : ℕ) :
    ArithmeticSize.Bound base ((budget C).eval m) ((R.lam C a b m)^m) := by
  have h := formula_bound base a b c embed he (P.desired (R.stageLength C m) m)
  rw [P.eval_desired] at h
  exact h.mono (embed 5) (he 5) (by
    rw [budget_eval]
    exact P.size_desired_le (R.stageLength C m) m)

variable [Algebra ℚ K] [Fintype I] {d : ℕ} (F : FixedField K d) (coords : I→Fin d→ℚ)
variable (hc : ∀i,F.decode (coords i)=base i)

include he hc in
theorem parameter_word_heights (C m : ℕ) :
    (F.encoding.encode (R.lam C a b m)).length≤
      ArithmeticSize.bitBound F coords ((parameterBudget C).eval m) ∧
    (F.encoding.encode (R.mu C a b c m)).length≤
      ArithmeticSize.bitBound F coords ((parameterBudget C).eval m) ∧
    (F.encoding.encode (R.nu C a b c m)).length≤
      ArithmeticSize.bitBound F coords ((parameterBudget C).eval m) := by
  have h := parameters_bound base a b c embed he C m
  have hbase : (fun i=>F.decode (coords i))=base := funext hc
  rw [←hbase] at h
  exact ⟨h.1.encoded_length_le F coords,h.2.1.encoded_length_le F coords,
    h.2.2.encoded_length_le F coords⟩

include he hc in
theorem root_word_height (C m : ℕ) {ij : ℕ×ℕ} (hij : ij.1+ij.2≤m) :
    (F.encoding.encode (R.root C a b c (m,ij))).length≤
      ArithmeticSize.bitBound F coords ((budget C).eval m) := by
  have h := root_bound base a b c embed he C m hij
  have hbase : (fun i=>F.decode (coords i))=base := funext hc
  rw [←hbase] at h
  exact h.encoded_length_le F coords

include he hc in
theorem desired_word_height (C m : ℕ) :
    (F.encoding.encode ((R.lam C a b m)^m)).length≤
      ArithmeticSize.bitBound F coords ((budget C).eval m) := by
  have h := desired_bound base a b c embed he C m
  have hbase : (fun i=>F.decode (coords i))=base := funext hc
  rw [←hbase] at h
  exact h.encoded_length_le F coords

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicProgrammeRootBounds
