import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Differences

/-! Recover exponent zero from positive samples without spectral separation.
All exponential nodes are nonzero. The first arithmetic sample is set to
zero, and the annihilator recurrence solves for the missing true value. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ZeroExtrapolation
open scoped BigOperators
namespace D
export GlobalCloseCompletionComplementQ4Differences
  (difference process processList samples process_samples process_add process_sum factor factor_zero factor_nonzero)
end D
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K ι : Type} [Field K]

def zeroed (f : ℕ→K) : ℕ→K:=fun k=>if k=0 then 0 else f k

theorem process_powers (roots : List K) (coefficient node : K) (k : ℕ) :
    D.process roots (fun k=>coefficient*node^k) k=coefficient*node^k*D.factor roots node := by
  induction roots generalizing coefficient with
  | nil=>simp [D.process,D.factor]
  | cons root roots ih=>
    change D.process roots (D.difference root (fun k=>coefficient*node^k)) k=_
    have localForm : D.difference root (fun k=>coefficient*node^k)=
        fun k=>(coefficient*(node-root))*node^k := by
      funext k
      simp only [D.difference,pow_succ]
      ring
    rw [localForm,ih]
    simp only [D.factor,List.map_cons,List.prod_cons]
    ring

theorem split (f : ℕ→K) : f=fun k=>zeroed f k+f 0*(0:K)^k := by
  funext k
  cases k <;> simp [zeroed]

theorem zeroed_value (roots : List K) (f : ℕ→K) (annihilated : D.process roots f 0=0) :
    D.process roots (zeroed f) 0= -f 0*D.factor roots 0 := by
  have h:=congrArg (fun g : ℕ→K=>D.process roots g 0) (split f)
  rw [D.process_add] at h
  dsimp only at h
  rw [process_powers] at h
  simp only [pow_zero,mul_one,annihilated] at h
  linear_combination -h

theorem annihilated [Fintype ι] (roots : List K) (nodes coefficients : ι→K)
    (covered : ∀i,nodes i∈roots) :
    D.process roots (fun k=>∑i,coefficients i*nodes i^k) 0=0 := by
  rw [D.process_sum]
  simp only [process_powers,pow_zero,mul_one]
  have killed (i : ι) : D.factor roots (nodes i)=0:=D.factor_zero roots (nodes i) (covered i)
  simp_rw [killed,mul_zero]
  simp

theorem isolate [Fintype ι] (roots : List K) (nodes coefficients : ι→K)
    (covered : ∀i,nodes i∈roots) :
    D.processList roots (D.samples (zeroed (fun k=>∑i,coefficients i*nodes i^k)) 0 (roots.length+1))=
      [-(∑i,coefficients i)*D.factor roots 0] := by
  rw [D.process_samples,zeroed_value roots _ (annihilated roots nodes coefficients covered)]
  simp only [pow_zero,mul_one]

theorem recover [Fintype ι] (roots : List K) (nodes coefficients : ι→K)
    (covered : ∀i,nodes i∈roots) (nonzero : ∀root∈roots,root≠0) :
    -(D.processList roots (D.samples (zeroed (fun k=>∑i,coefficients i*nodes i^k))
      0 (roots.length+1))).headD 0 / D.factor roots 0=∑i,coefficients i := by
  rw [isolate roots nodes coefficients covered]
  simp only [List.headD_cons,neg_mul,neg_neg]
  exact mul_div_cancel_right₀ _ (D.factor_nonzero roots 0 (fun root member=>(nonzero root member).symm))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ZeroExtrapolation
end
