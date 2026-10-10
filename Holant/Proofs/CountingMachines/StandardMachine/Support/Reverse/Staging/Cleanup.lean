import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.HeterogeneousSum

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Actual total erasure of every heterogeneous tape,
including unused and input/output tapes, followed by one encoded verdict.
The key order is a fixed finite table; no list/tape assignment is an opcode. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Cleanup
open Turing Holant.Complexity
open scoped BigOperators
variable {K : Type} [DecidableEq K] [Fintype K] (Γ : K → Type)
    [∀ k, Fintype (Γ k)] (input output : K) (encode : Bool → Γ output)

abbrev Label := Fin (Fintype.card K + 1)
abbrev State := Bool × Bool

def key (i : Label (K := K)) (h : i.val < Fintype.card K) : K :=
  (Fintype.equivFin K).symm ⟨i.val,h⟩

def next (i : Label (K := K)) (h : i.val < Fintype.card K) : Label (K := K) :=
  ⟨i.val+1,by omega⟩

def program (i : Label (K := K)) : TM2.Stmt Γ (Label (K := K)) State :=
  if h : i.val < Fintype.card K then
    .pop (key i h) (fun v b => (b.isSome,v.2))
      (.branch Prod.fst
        (.load (fun v => (false,v.2)) (.goto (fun _ => i)))
        (.load (fun v => (false,v.2)) (.goto (fun _ => next i h))))
  else .push output (fun v => encode v.2) (.load (fun _ => (false,false)) .halt)

def computer : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := Γ
  Λ := Label (K := K)
  main := 0
  σ := State
  initialState := (false,false)
  m := program Γ output encode

def cfg (i : Label (K := K)) (verdict : Bool) (S : ∀ k, List (Γ k)) :
    (computer Γ input output encode).Cfg := ⟨some i,(false,verdict),S⟩

theorem step_cons (i : Label (K := K)) (h : i.val < Fintype.card K)
    (verdict : Bool) (a : Γ (key i h)) (word : List (Γ (key i h)))
    (S : ∀ k, List (Γ k)) :
    (computer Γ input output encode).step
      (cfg Γ input output encode i verdict (Function.update S (key i h) (a::word))) =
        some (cfg Γ input output encode i verdict (Function.update S (key i h) word)) := by
  simp [FinTM2.step,TM2.step,computer,program,cfg,h,TM2.stepAux,
    Function.update_idem]

theorem step_nil (i : Label (K := K)) (h : i.val < Fintype.card K)
    (verdict : Bool) (S : ∀ k, List (Γ k)) :
    (computer Γ input output encode).step
      (cfg Γ input output encode i verdict (Function.update S (key i h) [])) =
        some (cfg Γ input output encode (next i h) verdict
          (Function.update S (key i h) [])) := by
  simp [FinTM2.step,TM2.step,computer,program,cfg,h,TM2.stepAux,
    Function.update_idem]

theorem clear_key (i : Label (K := K)) (h : i.val < Fintype.card K)
    (verdict : Bool) (word : List (Γ (key i h))) (S : ∀ k, List (Γ k)) :
    (fun p => p.bind (computer Γ input output encode).step)^[word.length+1]
      (some (cfg Γ input output encode i verdict (Function.update S (key i h) word))) =
        some (cfg Γ input output encode (next i h) verdict
          (Function.update S (key i h) [])) := by
  induction word with
  | nil => simpa using step_nil Γ input output encode i h verdict S
  | cons a word ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,
      Option.bind_some,step_cons]
    exact ih

theorem final_step (i : Label (K := K)) (h : i.val = Fintype.card K)
    (verdict : Bool) :
    (computer Γ input output encode).step (cfg Γ input output encode i verdict (fun _ => [])) =
      some (haltList (computer Γ input output encode) [encode verdict]) := by
  have hi : ¬ i.val < Fintype.card K := by omega
  simp only [FinTM2.step,TM2.step,computer,program,cfg,hi,dite_false,ite_false,TM2.stepAux,haltList]
  congr 2
  funext k
  by_cases h : k = output
  · subst k; simp
  · simp [h]

/-- The induction invariant says only which earlier literal pop loops have
already completed. The public `clean_run` produces this invariant from index 0.
-/
theorem finish_run (n : ℕ) (i : Label (K := K))
    (hi : i.val+n = Fintype.card K) (verdict : Bool) (S : ∀ k, List (Γ k))
    (B : ℕ) (hB : ∀ k, (S k).length ≤ B)
    (hclean : ∀ k, (Fintype.equivFin K k).val < i.val → S k = []) :
    ∃ t, t ≤ n*(B+1)+1 ∧
      (fun p => p.bind (computer Γ input output encode).step)^[t]
        (some (cfg Γ input output encode i verdict S)) =
          some (haltList (computer Γ input output encode) [encode verdict]) := by
  induction n generalizing i S with
  | zero =>
    have hS : S = (fun _ => []) := by
      funext k
      exact hclean k (by have := (Fintype.equivFin K k).isLt; omega)
    subst S
    exact ⟨1,by simp,by simpa using final_step Γ input output encode i (by omega) verdict⟩
  | succ n ih =>
    have hlt : i.val < Fintype.card K := by omega
    let k := key i hlt
    let S' := Function.update S k []
    have hB' : ∀ j, (S' j).length ≤ B := by
      intro j
      by_cases hj : j = k
      · subst j; simp [S']
      · simpa [S',hj] using hB j
    have hclean' : ∀ j, (Fintype.equivFin K j).val < (next i hlt).val → S' j = [] := by
      intro j hj
      by_cases hjk : j = k
      · subst j; simp [S']
      · have hne : (Fintype.equivFin K j).val ≠ i.val := by
          intro he
          apply hjk
          apply (Fintype.equivFin K).injective
          apply Fin.ext
          simpa [k,key] using he
        have hjold : (Fintype.equivFin K j).val < i.val := by
          simp only [next] at hj
          omega
        simpa [S',hjk] using hclean j hjold
    obtain ⟨t,ht,hr⟩ := ih (next i hlt) (by simp only [next]; omega) S' hB' hclean'
    have hc := clear_key Γ input output encode i hlt verdict (S k) S
    have hu : Function.update S k (S k) = S := Function.update_eq_self k S
    refine ⟨(S k).length+1+t,?_,?_⟩
    · have hlen := hB k
      simp only [Nat.succ_mul]
      omega
    · rw [show (S k).length+1+t = t+((S k).length+1) by omega,
        Function.iterate_add_apply]
      have hrun := (congrArg
        ((fun p => p.bind (computer Γ input output encode).step)^[t]) hc).trans hr
      simpa only [k,S',hu] using hrun

theorem clean_run (verdict : Bool) (S : ∀ k, List (Γ k)) :
    ∃ t, t ≤ Fintype.card K*((∑ k, (S k).length)+1)+1 ∧
      (fun p => p.bind (computer Γ input output encode).step)^[t]
        (some (cfg Γ input output encode 0 verdict S)) =
          some (haltList (computer Γ input output encode) [encode verdict]) := by
  apply finish_run Γ input output encode (Fintype.card K) 0 (by simp) verdict S
  · intro k
    exact Finset.single_le_sum (f := fun j => (S j).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  · intro k hk
    simp at hk

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Cleanup
