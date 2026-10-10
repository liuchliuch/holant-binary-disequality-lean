import Holant.ReedMuller.CoefficientAtlas.Code

namespace Holant.ReedMuller.CoefficientAtlas
open Holant.ReedMuller.LowArity
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

def pairPoints : Fin 28 → Fin 2 → Point := ![![0,1],![0,2],![0,3],![0,4],![0,5],![0,6],![0,7],![1,2],![1,3],![1,4],![1,5],![1,6],![1,7],![2,3],![2,4],![2,5],![2,6],![2,7],![3,4],![3,5],![3,6],![3,7],![4,5],![4,6],![4,7],![5,6],![5,7],![6,7]]
def portOrder : Fin 28 → Fin 8 → Point := ![![0,1,2,3,4,5,6,7],![0,2,1,3,4,6,5,7],![0,3,1,2,4,7,5,6],![0,4,1,5,2,6,3,7],![0,5,1,4,2,7,3,6],![0,6,1,7,2,4,3,5],![0,7,1,6,2,5,3,4],![1,2,0,3,4,7,5,6],![1,3,0,2,4,6,5,7],![1,4,0,5,2,7,3,6],![1,5,0,4,2,6,3,7],![1,6,0,7,2,5,3,4],![1,7,0,6,2,4,3,5],![2,3,0,1,4,5,6,7],![2,4,0,6,1,7,3,5],![2,5,0,7,1,6,3,4],![2,6,0,4,1,5,3,7],![2,7,0,5,1,4,3,6],![3,4,0,7,1,6,2,5],![3,5,0,6,1,7,2,4],![3,6,0,5,1,4,2,7],![3,7,0,4,1,5,2,6],![4,5,0,1,2,3,6,7],![4,6,0,2,1,3,5,7],![4,7,0,3,1,2,5,6],![5,6,0,3,1,2,4,7],![5,7,0,2,1,3,4,6],![6,7,0,1,2,3,4,5]]
def portInverse : Fin 28 → Point → Fin 8 := ![![0,1,2,3,4,5,6,7],![0,2,1,3,4,6,5,7],![0,2,3,1,4,6,7,5],![0,2,4,6,1,3,5,7],![0,2,4,6,3,1,7,5],![0,2,4,6,5,7,1,3],![0,2,4,6,7,5,3,1],![2,0,1,3,4,6,7,5],![2,0,3,1,4,6,5,7],![2,0,4,6,1,3,7,5],![2,0,4,6,3,1,5,7],![2,0,4,6,7,5,1,3],![2,0,4,6,5,7,3,1],![2,3,0,1,4,5,6,7],![2,4,0,6,1,7,3,5],![2,4,0,6,7,1,5,3],![2,4,0,6,3,5,1,7],![2,4,0,6,5,3,7,1],![2,4,6,0,1,7,5,3],![2,4,6,0,7,1,3,5],![2,4,6,0,5,3,1,7],![2,4,6,0,3,5,7,1],![2,3,4,5,0,1,6,7],![2,4,3,5,0,6,1,7],![2,4,5,3,0,6,7,1],![2,4,5,3,6,0,1,7],![2,4,3,5,6,0,7,1],![2,3,4,5,6,7,0,1]]
theorem port_left_inv : ∀ p i, portInverse p (portOrder p i)=i := by decide
theorem port_right_inv : ∀ p i, portOrder p (portInverse p i)=i := by decide
def ports (p : Fin 28) : Fin 8 ≃ Point := ⟨portOrder p,portInverse p,port_left_inv p,port_right_inv p⟩
def generatorCodes : Fin 28 → Fin 3 → ℕ := ![![9,5,13],![9,3,11],![9,7,15],![5,3,7],![5,11,15],![13,3,15],![13,11,7],![9,14,6],![9,10,2],![5,14,10],![5,6,2],![13,6,10],![13,14,2],![9,12,4],![3,14,12],![11,6,12],![3,6,4],![11,14,4],![7,10,12],![15,2,12],![15,10,4],![7,2,4],![5,12,8],![3,10,8],![7,14,8],![15,6,8],![11,2,8],![13,4,8]]
def generators (p : Fin 28) (i : Fin 3) : Param := bits 4 (generatorCodes p i)

def lift (p : Fin 28) (t : Fin 3 → Bool) : Param :=
  ∑ i, if t i then generators p i else 0

def repeatedWord (t : Fin 3 → Bool) : Fin 6 → Bool := ![t 0,t 0,t 1,t 1,t 2,t 2]

def fill (p : Fin 28) (b : Bool) (y : Fin 6 → Bool) : Point → Bool :=
  fun x => ![b,b,y 0,y 1,y 2,y 3,y 4,y 5] ((ports p).symm x)

def Plane (a : Param) : Prop := a≠0 ∧ a≠oneParam
instance (a : Param) : Decidable (Plane a) := by unfold Plane; infer_instance

theorem pairPoints_complete : ∀ i j : Point, i≠j →
    ∃ p : Fin 28, (pairPoints p 0=i ∧ pairPoints p 1=j) ∨
      (pairPoints p 0=j ∧ pairPoints p 1=i) := by decide

theorem port_endpoints : ∀ p, ports p 0=pairPoints p 0 ∧ ports p 1=pairPoints p 1 := by decide

theorem generators_plane : ∀ p i, Plane (generators p i) := by decide

theorem generator_sum : ∀ p, (∑ i : Fin 3, generators p i)=oneParam := by decide

theorem generators_injective : ∀ p, Function.Injective (generators p) := by decide

theorem plane_pair_covered : ∀ a b : Param, Plane a → Plane b → a≠b → a+b≠oneParam →
    ∃ p : Fin 28, ∃ i j : Fin 3, i≠j ∧ generators p i=a ∧ generators p j=b := by decide

theorem plane_occurs : ∀ a : Param, Plane a → ∃ p : Fin 28, ∃ i : Fin 3, generators p i=a := by decide

theorem plane_companion : ∀ a : Param, Plane a →
    ∃ b : Param, Plane b ∧ a≠b ∧ a+b≠oneParam := by decide

/-- Every projected matching word has exactly one nonzero-support lift. This
is a literal ordered-port identity, including every cancellation possibility. -/
theorem unique_card_lift : ∀ p : Fin 28, ∀ t : Fin 3 → Bool,
    (fill p false (repeatedWord t)=word (lift p t) ∧ ∀ a : Param, fill p true (repeatedWord t)≠word a) ∨
    (fill p true (repeatedWord t)=word (lift p t) ∧ ∀ a : Param, fill p false (repeatedWord t)≠word a) := by decide

theorem lift_zero : ∀ p, lift p (fun _ => false)=0 := by decide

theorem lift_single : ∀ p i, lift p (fun j => decide (j=i))=generators p i := by decide

theorem lift_pair : ∀ p i j, i≠j →
    lift p (fun k => decide (k=i ∨ k=j))=generators p i+generators p j := by decide

theorem lift_all : ∀ p, lift p (fun _ => true)=oneParam := by decide

theorem add_self_zero : ∀ a : Param, a+a=0 := by decide

theorem add_cancel : ∀ a b : Param, (a+b)+a=b := by decide

theorem plane_sum : ∀ a b : Param, Plane a → Plane b → a≠b → a+b≠oneParam → Plane (a+b) := by decide

theorem lift_complement : ∀ p i, lift p (fun j => decide (j≠i))=oneParam+generators p i := by decide

end Holant.ReedMuller.CoefficientAtlas
