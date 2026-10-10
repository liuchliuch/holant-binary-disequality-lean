import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch.Enumeration


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes)

abbrev Context := Scan.Context
abbrev contextEncoding := Scan.contextEncoding
abbrev Request := Context × ℕ
abbrev requestEncoding := pairEncoding contextEncoding encodingNatBool

def stage (r : Request) : Option Bool := Scan.first r.1 (Enumeration.candidates r.2)

theorem stage_sound {r : Request} {b : Bool} {z : ℂ}
    (hz : r.1.1.Represents z) (hb : stage r=some b) :
    b=true ↔ Polynomial.aeval z r.1.2.polynomial=0 := Scan.first_sound hz hb

/-- Validity names the SAME root throughout. Neither a minimal relation nor
an accepted evidence nor a stopping height is an input premise. -/
theorem eventually (x : Context) (hv : Valid x.1) :
    ∃ H, ∀ h ≥ H, (stage (x,h)).isSome=true := by
  obtain ⟨z,hz⟩ := hv
  obtain ⟨e,he⟩ := check_complete hz x.2
  obtain ⟨H,hH⟩ := Enumeration.covers e
  refine ⟨H,fun h hh => ?_⟩
  have hm : e.zero ∈ Scan.values x (Enumeration.candidates h) :=
    Scan.mem_values.mpr ⟨e,hH h hh,he,rfl⟩
  cases hs : Scan.values x (Enumeration.candidates h) with
  | nil => simp only [hs,List.not_mem_nil] at hm
  | cons b bs => simp only [stage,Scan.first,hs,List.head?_cons,Option.isSome_some]

/-- Finite induction in Prop finds the first successful stage in a proved
finite prefix. It is not a runtime search function or a new controller. -/
private theorem first_in_prefix (f : ℕ → Option Bool) (H : ℕ)
    (hs : ∃ b, f H=some b) :
    ∃ n ≤ H, ∃ b, f n=some b ∧ ∀ j < n, f j=none := by
  induction H generalizing f with
  | zero =>
    obtain ⟨b,hb⟩ := hs
    exact ⟨0,le_rfl,b,hb,fun j hj => False.elim (Nat.not_lt_zero j hj)⟩
  | succ H ih =>
    cases h₀ : f 0 with
    | some b => exact ⟨0,Nat.zero_le _,b,h₀,fun j hj => False.elim (Nat.not_lt_zero j hj)⟩
    | none =>
      obtain ⟨n,hn,b,hb,hbefore⟩ := ih (fun j => f (j+1)) hs
      refine ⟨n+1,Nat.succ_le_succ hn,b,hb,?_⟩
      intro j hj
      cases j with
      | zero => exact h₀
      | succ j => exact hbefore j (Nat.lt_of_succ_lt_succ hj)

theorem first_success (x : Context) (hv : Valid x.1) :
    ∃ n b, stage (x,n)=some b ∧ ∀ j < n, stage (x,j)=none := by
  obtain ⟨H,hH⟩ := eventually x hv
  have hs : ∃ b, stage (x,H)=some b := by
    cases hh : stage (x,H) with
    | none => have hf := hH H le_rfl; simp only [hh,Option.isSome_none,Bool.false_eq_true] at hf
    | some b => exact ⟨b,rfl⟩
  obtain ⟨n,_,b,hb,hbefore⟩ := first_in_prefix (fun h => stage (x,h)) H hs
  exact ⟨n,b,hb,hbefore⟩

noncomputable section
def stageExecutes : Executes requestEncoding Scan.resultEncoding stage :=
  ((Executes.ofComputes (Wiring.firstComputes contextEncoding encodingNatBool)).pair
    ((Executes.ofComputes (Wiring.secondComputes contextEncoding encodingNatBool)).comp
      Enumeration.executes)).comp Physical.scan

def stage_outputs (r : Request) : TM2OutputsInTime stageExecutes.machine.computer
    (requestEncoding.encode r) (some (Scan.resultEncoding.encode (stage r))) (stageExecutes.cost r) :=
  stageExecutes.outputs r

theorem stage_primitives (r : Request) : primitiveCost stageExecutes.machine (stage_outputs r).steps
    (some (initList stageExecutes.machine.computer (requestEncoding.encode r))) ≤
      stageExecutes.cost r*stageExecutes.machine.primitiveBudget := stageExecutes.primitive_bound r
end
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch
