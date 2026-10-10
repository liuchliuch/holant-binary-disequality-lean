import Holant.Dihedral.TwoCardLocalization.Program

namespace Holant.Dihedral.TwoCardLocalization
open Holant
variable {I J K : Type*} [Field K]

def Program.map (f : I → J) {n m : ℕ} : Program I n m → Program J n m
  | .done n => .done n
  | .step p i rest => .step p (f i) (rest.map f)

@[simp] theorem Program.map_length (f : I → J) {n m : ℕ} (P : Program I n m) :
    (P.map f).length=P.length := by induction P <;> simp_all [map,length]

@[simp] theorem Program.map_residual (f : I → J) (C : J → Kernel K) {n m : ℕ}
    (P : Program I n m) (q : Signature K n) :
    (P.map f).residual C q=P.residual (fun i => C (f i)) q := by
  induction P with
  | done n => rfl
  | step p i rest ih => exact ih _

@[simp] theorem Program.map_core (f : I → J) (C : J → Kernel K) {n m : ℕ}
    (P : Program I n m) (q : Signature K (n+2)) :
    (P.map f).core C q=P.core (fun i => C (f i)) q := by
  induction P with
  | done n => rfl
  | step p i rest ih => exact ih _

end Holant.Dihedral.TwoCardLocalization
