import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Annihilator

/-! Operational annihilation by successive sequence differences. A list of
D roots shrinks D+1 positive samples to one value using only adjacent
subtractions and multiplications. Repeated roots are retained exactly. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Differences
open scoped BigOperators
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K ι : Type} [Field K]

def difference (node : K) (f : ℕ→K) : ℕ→K:=fun k=>f (k+1)-node*f k
def process (roots : List K) (f : ℕ→K) : ℕ→K:=
  roots.foldl (fun g node=>difference node g) f
def pass (node : K) : List K→List K
  | a::b::rest=>(b-node*a)::pass node (b::rest)
  | _=>[]
def processList (roots values : List K) : List K:=roots.foldl (fun values node=>pass node values) values
def samples (f : ℕ→K) (start : ℕ) : ℕ→List K
  | 0=>[]
  | n+1=>f start::samples f (start+1) n
def factor (roots : List K) (target : K) : K:=(roots.map (fun node=>target-node)).prod

theorem pass_samples (node : K) (f : ℕ→K) (start n : ℕ) :
    pass node (samples f start (n+1))=samples (difference node f) start n := by
  induction n generalizing start with
  | zero=>rfl
  | succ n ih=>
    change difference node f start :: pass node (samples f (start+1) (n+1))=
      difference node f start :: samples (difference node f) (start+1) n
    rw [ih]

theorem process_samples (roots : List K) (f : ℕ→K) (start : ℕ) :
    processList roots (samples f start (roots.length+1))=[process roots f start] := by
  induction roots generalizing f with
  | nil=>rfl
  | cons node roots ih=>
    simp only [processList,List.foldl_cons,List.length_cons,Nat.add_assoc,
      show 1+1=2 from rfl,process]
    rw [pass_samples]
    exact ih (difference node f)

theorem process_add (roots : List K) (f g : ℕ→K) :
    process roots (fun k=>f k+g k)=fun k=>process roots f k+process roots g k := by
  induction roots generalizing f g with
  | nil=>rfl
  | cons node roots ih=>
    change process roots (difference node (fun k=>f k+g k))=_
    have h : difference node (fun k=>f k+g k)=fun k=>difference node f k+difference node g k := by
      funext k
      simp only [difference]
      ring
    rw [h,ih]
    rfl

theorem process_sum [Fintype ι] (roots : List K) (f : ι→ℕ→K) :
    process roots (fun k=>∑i,f i k)=fun k=>∑i,process roots (f i) k := by
  classical
  induction roots generalizing f with
  | nil=>rfl
  | cons node roots ih=>
    change process roots (difference node (fun k=>∑i,f i k))=_
    have h : difference node (fun k=>∑i,f i k)=fun k=>∑i,difference node (f i) k := by
      funext k
      simp [difference,Finset.mul_sum,Finset.sum_sub_distrib]
    rw [h,ih]
    rfl

theorem process_exp (roots : List K) (coefficient target : K) (k : ℕ) :
    process roots (fun k=>coefficient*target^(k+1)) k=coefficient*target^(k+1)*factor roots target := by
  induction roots generalizing coefficient with
  | nil=>simp [process,factor]
  | cons node roots ih=>
    change process roots (difference node (fun k=>coefficient*target^(k+1))) k=_
    have h : difference node (fun k=>coefficient*target^(k+1))=
        fun k=>(coefficient*(target-node))*target^(k+1) := by
      funext k
      simp only [difference,pow_succ]
      ring
    rw [h,ih]
    simp only [factor,List.map_cons,List.prod_cons]
    ring

theorem factor_zero (roots : List K) (node : K) (member : node∈roots) : factor roots node=0 := by
  apply List.prod_eq_zero_iff.mpr
  exact List.mem_map.mpr ⟨node,member,sub_self _⟩
theorem factor_nonzero (roots : List K) (target : K) (separate : ∀node∈roots,target≠node) : factor roots target≠0 := by
  intro zero
  have member : (0:K)∈roots.map (fun node=>target-node):=List.prod_eq_zero_iff.mp zero
  obtain ⟨node,member,equal⟩:=List.mem_map.mp member
  exact separate node member (sub_eq_zero.mp equal)

theorem isolate [Fintype ι] (roots : List K) (nodes coefficients : ι→K)
    (covered : ∀i,nodes i∈roots) (target answer : K) :
    processList roots (samples (fun k=>answer*target^(k+1)+∑i,coefficients i*nodes i^(k+1)) 0 (roots.length+1))=
      [answer*target*factor roots target] := by
  rw [process_samples,process_add,process_sum]
  simp only [process_exp,pow_one]
  simp_rw [factor_zero roots _ (covered _),mul_zero]
  simp

theorem recover [Fintype ι] (roots : List K) (nodes coefficients : ι→K)
    (covered : ∀i,nodes i∈roots) (target answer : K) (targetNonzero : target≠0)
    (separate : ∀node∈roots,target≠node) :
    (processList roots (samples (fun k=>answer*target^(k+1)+∑i,coefficients i*nodes i^(k+1))
      0 (roots.length+1))).headD 0 / (target*factor roots target)=answer := by
  rw [isolate roots nodes coefficients covered target answer]
  simp only [List.headD_cons]
  rw [mul_assoc,mul_div_cancel_right₀ _ (mul_ne_zero targetNonzero (factor_nonzero roots target separate))]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Differences
end
