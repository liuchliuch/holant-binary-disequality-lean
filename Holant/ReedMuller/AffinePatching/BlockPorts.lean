import Holant.ReedMuller.AffinePatching.Summation

/-! The actual first-variable summation convention with explicit original
prefix and surviving suffix coordinate embeddings. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase
noncomputable section
set_option backward.isDefEq.respectTransparency false

def prefixPort (m : ℕ) : (n : ℕ) → Fin n → Fin (m+n)
  | 0,i => Fin.elim0 i
  | n+1,i => Fin.cases 0 (fun j => (prefixPort m n j).succ) i

def suffixPort (m : ℕ) : (n : ℕ) → Fin m → Fin (m+n)
  | 0,i => i
  | n+1,i => (suffixPort m n i).succ

@[simp] theorem insertWord_prefix (m n : ℕ) (y : Word n) (x : Word m) (i : Fin n) :
    insertWord m n y x (prefixPort m n i)=y i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih (Fin.tail y) j

@[simp] theorem insertWord_suffix (m n : ℕ) (y : Word n) (x : Word m) (i : Fin m) :
    insertWord m n y x (suffixPort m n i)=x i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (Fin.tail y)

end
end Holant.ReedMuller.AffinePatching
