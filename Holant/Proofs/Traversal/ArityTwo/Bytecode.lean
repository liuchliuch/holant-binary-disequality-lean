import Holant.Proofs.Traversal.ArityTwo.Transfer
import Holant.OneHot.StackProgram.Core


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo
open Holant Holant.OneHot.StackProgram
variable {A K : Type*} [CommSemiring K]

def dotTrace (p q x y : K) : List K :=
  [p,x,p*x,q,y,q*y,q*y,p*x,q*y+p*x]

def matrixStep (M : Kernel A) : Code A :=
  [.copy 0,.literal (M true false),.mul,.copy 2,.literal (M true true),.mul,.add,
   .copy 1,.literal (M false false),.mul,.copy 3,.literal (M false true),.mul,.add,
   .erase 2,.erase 2]

def matrixTrace (coeff : A → K) (M : Kernel A) (v : Bool → K) : List K :=
  dotTrace (coeff (M true false)) (coeff (M true true)) (v false) (v true) ++
  dotTrace (coeff (M false false)) (coeff (M false true)) (v false) (v true)

theorem run_matrixStep (coeff : A → K) (M : Kernel A) (v : Bool → K) (s : List K) :
    run coeff (matrixStep M) (v false::v true::s) =
      some (Kernel.act (realizeMatrix coeff M) v false :: Kernel.act (realizeMatrix coeff M) v true :: s,
        matrixTrace coeff M v) := by
  simp [matrixStep,run,step,eraseAt,matrixTrace,dotTrace,realizeMatrix,Kernel.act_apply,add_comm]

def transferCode : List (Kernel A) → Code A
  | [] => []
  | M::ms => transferCode ms ++ matrixStep M

def transferTrace (coeff : A → K) (v : Bool → K) : List (Kernel A) → List K
  | [] => []
  | M::ms => transferTrace coeff v ms ++ matrixTrace coeff M (message (ms.map (realizeMatrix coeff)) v)

theorem run_transfer (coeff : A → K) (ms : List (Kernel A)) (v : Bool → K) (s : List K) :
    run coeff (transferCode ms) (v false::v true::s) =
      some (message (ms.map (realizeMatrix coeff)) v false ::
        message (ms.map (realizeMatrix coeff)) v true :: s,transferTrace coeff v ms) := by
  induction ms with
  | nil => simp [transferCode,transferTrace,run]
  | cons M ms ih =>
    have h := run_append_of coeff ih
      (run_matrixStep coeff M (message (ms.map (realizeMatrix coeff)) v) s)
    simpa only [transferCode,transferTrace,List.map_cons,message_cons] using h

def dotCode (l : Bool → A) : Code A :=
  [.literal (l false),.mul,.swap,.literal (l true),.mul,.add]

theorem run_dot (coeff : A → K) (l : Bool → A) (v : Bool → K) (s : List K) :
    run coeff (dotCode l) (v false::v true::s) =
      some ((coeff (l false)*v false+coeff (l true)*v true)::s,
        dotTrace (coeff (l false)) (coeff (l true)) (v false) (v true)) := by
  simp [dotCode,run,step,dotTrace,add_comm]

def pathCode (l : Bool → A) (ms : List (Kernel A)) (r : Bool → A) : Code A :=
  [.literal (r true),.literal (r false)] ++ transferCode ms ++ dotCode l

def pathTrace (coeff : A → K) (l : Bool → A) (ms : List (Kernel A)) (r : Bool → A) : List K :=
  transferTrace coeff (fun b => coeff (r b)) ms ++
  dotTrace (coeff (l false)) (coeff (l true))
    (message (ms.map (realizeMatrix coeff)) (fun b => coeff (r b)) false)
    (message (ms.map (realizeMatrix coeff)) (fun b => coeff (r b)) true)

theorem run_path (coeff : A → K) (l : Bool → A) (ms : List (Kernel A)) (r : Bool → A) (s : List K) :
    run coeff (pathCode l ms r) s =
      some (pathValue (fun b => coeff (l b)) (ms.map (realizeMatrix coeff)) (fun b => coeff (r b)) :: s,
        pathTrace coeff l ms r) := by
  have hi : run coeff [.literal (r true),.literal (r false)] s =
      some (coeff (r false)::coeff (r true)::s,[]) := rfl
  have h := run_append_of coeff (run_append_of coeff hi (run_transfer coeff ms (fun b => coeff (r b)) s))
    (run_dot coeff l (message (ms.map (realizeMatrix coeff)) (fun b => coeff (r b))) s)
  simpa [pathCode,pathTrace,pathValue,add_comm] using h

def columnCode (ms : List (Kernel A)) (b : Bool) : Code A :=
  (if b then [.one,.zero] else [.zero,.one]) ++ transferCode ms ++
    [if b then .erase 0 else .erase 1]

theorem run_column (coeff : A → K) (ms : List (Kernel A)) (b : Bool) (s : List K) :
    run coeff (columnCode ms b) s =
      some (product (ms.map (realizeMatrix coeff)) b b :: s,transferTrace coeff (basis b) ms) := by
  cases b with
  | false =>
    have hi : run coeff [.zero,.one] s = some (basis false false::basis false true::s,[]) := rfl
    have hm := run_append_of coeff hi (run_transfer coeff ms (basis false) s)
    have he : run coeff [.erase 1]
        (message (ms.map (realizeMatrix coeff)) (basis false) false ::
          message (ms.map (realizeMatrix coeff)) (basis false) true :: s) =
        some ([message (ms.map (realizeMatrix coeff)) (basis false) false]++s,[]) := rfl
    simpa [columnCode,message_basis] using run_append_of coeff hm he
  | true =>
    have hi : run coeff [.one,.zero] s = some (basis true false::basis true true::s,[]) := rfl
    have hm := run_append_of coeff hi (run_transfer coeff ms (basis true) s)
    have he : run coeff [.erase 0]
        (message (ms.map (realizeMatrix coeff)) (basis true) false ::
          message (ms.map (realizeMatrix coeff)) (basis true) true :: s) =
        some ([message (ms.map (realizeMatrix coeff)) (basis true) true]++s,[]) := rfl
    simpa [columnCode,message_basis] using run_append_of coeff hm he

def cycleCode (ms : List (Kernel A)) : Code A := columnCode ms false ++ columnCode ms true ++ [.add]

def cycleTrace (coeff : A → K) (ms : List (Kernel A)) : List K :=
  let M := product (ms.map (realizeMatrix coeff))
  transferTrace coeff (basis false) ms ++ transferTrace coeff (basis true) ms ++
    [M true true,M false false,M true true+M false false]

theorem run_cycle (coeff : A → K) (ms : List (Kernel A)) (s : List K) :
    run coeff (cycleCode ms) s = some (cycleValue (ms.map (realizeMatrix coeff))::s,cycleTrace coeff ms) := by
  have h := run_append_of coeff (run_column coeff ms false s)
    (run_column coeff ms true (product (ms.map (realizeMatrix coeff)) false false::s))
  have ha : run coeff [.add]
      (product (ms.map (realizeMatrix coeff)) true true ::
        product (ms.map (realizeMatrix coeff)) false false :: s) =
      some ((product (ms.map (realizeMatrix coeff)) true true+
        product (ms.map (realizeMatrix coeff)) false false)::s,
        [product (ms.map (realizeMatrix coeff)) true true,
         product (ms.map (realizeMatrix coeff)) false false,
         product (ms.map (realizeMatrix coeff)) true true+product (ms.map (realizeMatrix coeff)) false false]) := rfl
  simpa [cycleCode,cycleTrace,cycleValue,Kernel.trace,add_comm] using run_append_of coeff h ha

def Component.code : Component A → Code A
  | .scalar a => [.literal a]
  | .path l ms r => pathCode l ms r
  | .cycle M ms => cycleCode (M::ms)

def Component.trace (coeff : A → K) : Component A → List K
  | .scalar _ => []
  | .path l ms r => pathTrace coeff l ms r
  | .cycle M ms => cycleTrace coeff (M::ms)

theorem Component.run_code (coeff : A → K) (c : Component A) (s : List K) :
    run coeff c.code s = some (c.eval coeff::s,c.trace coeff) := by
  cases c with
  | scalar a => rfl
  | path l ms r => exact run_path coeff l ms r s
  | cycle M ms => exact run_cycle coeff (M::ms) s

@[simp] theorem transferCode_length (ms : List (Kernel A)) : (transferCode ms).length = 16*ms.length := by
  induction ms with
  | nil => rfl
  | cons M ms ih => simp [transferCode,matrixStep,ih]; omega

@[simp] theorem pathCode_length (l r : Bool → A) (ms : List (Kernel A)) :
    (pathCode l ms r).length = 16*ms.length+8 := by simp [pathCode,dotCode] <;> omega

@[simp] theorem cycleCode_length (ms : List (Kernel A)) :
    (cycleCode ms).length = 32*ms.length+7 := by simp [cycleCode,columnCode] <;> omega

end Holant.LocalDrafts.TraversalCompletion.ArityTwo
