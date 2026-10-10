import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Interface
import Holant.OneHot.StackProgram.Bounds

/-! The actual arithmetic trace of prepared component bytecode. No size
certificate is supplied by an input: the subsequent grammar induction derives it. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components.Evaluation
variable {A K : Type} [CommSemiring K] (coeff : A → K)

def componentProgram : Descriptor A → Arithmetic K K
  | .dense => pure 0
  | .tree a ts => (interpretForest coeff ts).closedProgram (coeff a)
  | .unicycle a ts b us => do
      let x ← (interpretForest coeff ts).closedProgram (coeff a)
      let y ← (interpretForest coeff us).closedProgram (coeff b)
      Arithmetic.addOp x y

def productProgram : List (Descriptor A) → Arithmetic K K
  | [] => pure 1
  | d :: ds => do
      let x ← componentProgram coeff d
      let y ← productProgram ds
      Arithmetic.mulOp x y

def value (ds : List (Descriptor A)) : K := (productProgram coeff ds).run.1

/-- Exact output and complete ordered arithmetic operands/results, with a preserved stack suffix. -/
theorem run_componentCode (d : Descriptor A) (suffix : List K) :
    run coeff (componentCode d) suffix =
      some ((componentProgram coeff d).run.1 :: suffix, (componentProgram coeff d).values) := by
  cases d with
  | dense => rfl
  | tree root children => exact run_compileClosed coeff root children suffix
  | unicycle root children other forest =>
    exact run_addCode coeff _ _ _ _ (run_compileClosed coeff root children)
      (run_compileClosed coeff other forest) suffix

/-- The exact right fold compiled by the component driver, including the empty unit. -/
theorem run_productCode (ds : List (Descriptor A)) (suffix : List K) :
    run coeff (productCode ds) suffix =
      some ((productProgram coeff ds).run.1 :: suffix, (productProgram coeff ds).values) := by
  induction ds generalizing suffix with
  | nil => rfl
  | cons d ds ih => exact run_mulCode coeff _ _ _ _ (run_componentCode coeff d) ih suffix

variable {L : Type}
mutual
/-- Every interpreted literal retains a direct original finite-label witness. -/
theorem tree_all (f : A → L) (P : L → Prop) (h : ∀ a, P (f a)) (t : Tree A) :
    (interpretTree f t).All P := by
  cases t with
  | node a b ts => exact ⟨h a, h b, forest_all f P h ts⟩
theorem forest_all (f : A → L) (P : L → Prop) (h : ∀ a, P (f a)) (ts : Forest A) :
    (interpretForest f ts).All P := by
  cases ts with
  | nil => trivial
  | cons p t ts => exact ⟨h p, tree_all f P h t, forest_all f P h ts⟩
end

end Holant.OneHot.StackProgram.GraphCodeMachine.Components.Evaluation
