import Holant.Proofs.Traversal.ArityTwo.Bounds


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo
open Holant Holant.OneHot.StackProgram Holant.OneHot.ArithmeticSize
variable {A B K : Type*} [CommSemiring K]

def componentsCode : List (Component A) → Code A
  | [] => [.one]
  | c::cs => c.code ++ componentsCode cs ++ [.mul]

def componentsTrace (coeff : A → K) : List (Component A) → List K
  | [] => []
  | c::cs => c.trace coeff ++ componentsTrace coeff cs ++
      [evaluateComponents coeff cs,c.eval coeff,evaluateComponents coeff cs*c.eval coeff]

theorem run_components (coeff : A → K) (cs : List (Component A)) (s : List K) :
    run coeff (componentsCode cs) s =
      some (evaluateComponents coeff cs::s,componentsTrace coeff cs) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    have h := run_append_of coeff (c.run_code coeff s) (ih (c.eval coeff::s))
    have hm : run coeff [.mul] (evaluateComponents coeff cs::c.eval coeff::s) =
        some ((evaluateComponents coeff cs*c.eval coeff)::s,
          [evaluateComponents coeff cs,c.eval coeff,evaluateComponents coeff cs*c.eval coeff]) := rfl
    simpa [componentsCode,componentsTrace,evaluateComponents,mul_comm] using run_append_of coeff h hm

def componentsBudget (cs : List (Component A)) : ℕ := (cs.map Component.budget).sum

theorem components_bound (family : B → K) (unit : B) (hunit : family unit = 1)
    (coeff : A → K) (hlit : ∀ a, Bound family 1 (coeff a)) (cs : List (Component A)) :
    Bound family (componentsBudget cs) (evaluateComponents coeff cs) ∧
      ∀ z ∈ componentsTrace coeff cs, Bound family (componentsBudget cs) z := by
  induction cs with
  | nil => exact ⟨Bound.one, by simp [componentsTrace]⟩
  | cons c cs ih =>
    have hc := Component.bound family unit hunit coeff hlit c
    have hm : Bound family (componentsBudget (c::cs))
        (evaluateComponents coeff cs*c.eval coeff) := by
      simpa [componentsBudget,Nat.add_comm] using ih.1.mul hc.1
    have hc' := hc.1.mono unit hunit
      (show c.budget ≤ componentsBudget (c::cs) by simp [componentsBudget])
    have ht' := ih.1.mono unit hunit
      (show componentsBudget cs ≤ componentsBudget (c::cs) by simp [componentsBudget])
    refine ⟨?_, ?_⟩
    · simpa [evaluateComponents,mul_comm] using hm
    · intro z hz
      simp only [componentsTrace,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with (hz | hz) | rfl | rfl | rfl
      · exact (hc.2 z hz).mono unit hunit (by simp [componentsBudget])
      · exact (ih.2 z hz).mono unit hunit (by simp [componentsBudget])
      · exact ht'
      · exact hc'
      · exact hm

theorem Component.code_length_le (c : Component A) : c.code.length+1 ≤ 16*c.budget := by
  cases c <;> simp [Component.code,Component.budget] <;> omega

theorem componentsCode_length_le (cs : List (Component A)) :
    (componentsCode cs).length ≤ 16*componentsBudget cs+1 := by
  induction cs with
  | nil => simp [componentsCode,componentsBudget]
  | cons c cs ih =>
    have hc := c.code_length_le
    simp only [componentsCode,List.length_append,List.length_cons,List.length_nil]
    simp only [componentsBudget,List.map_cons,List.sum_cons] at *
    omega

theorem Component.budget_le_code (c : Component A) : c.budget ≤ c.code.length := by
  cases c <;> simp [Component.code,Component.budget] <;> omega

theorem componentsBudget_le_code (cs : List (Component A)) :
    componentsBudget cs ≤ (componentsCode cs).length := by
  induction cs with
  | nil => simp [componentsCode,componentsBudget]
  | cons c cs ih =>
    have hc := c.budget_le_code
    simp only [componentsBudget,List.map_cons,List.sum_cons,componentsCode,
      List.length_append,List.length_cons,List.length_nil] at *
    omega

/-- Descriptor size counts every component and every stored matrix. -/
def Component.size : Component A → ℕ
  | .scalar _ => 1
  | .path _ ms _ => ms.length+1
  | .cycle _ ms => ms.length+2

def componentsSize (cs : List (Component A)) : ℕ := (cs.map Component.size).sum

theorem Component.budget_le_size (c : Component A) : c.budget ≤ 3*c.size := by
  cases c <;> simp [Component.budget,Component.size] <;> omega

theorem componentsBudget_le_size (cs : List (Component A)) :
    componentsBudget cs ≤ 3*componentsSize cs := by
  induction cs with
  | nil => simp [componentsBudget,componentsSize]
  | cons c cs ih =>
    have hc := c.budget_le_size
    simp only [componentsBudget,componentsSize,List.map_cons,List.sum_cons] at *
    omega

end Holant.LocalDrafts.TraversalCompletion.ArityTwo
