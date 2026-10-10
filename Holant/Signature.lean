import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi

/-! Boolean signatures with explicit ordered ports. -/

namespace Holant

abbrev Tensor (K : Type*) (ι : Type*) := (ι → Bool) → K
abbrev Signature (K : Type*) (n : ℕ) := Tensor K (Fin n)

namespace Tensor

variable {K ι κ ν : Type*}

@[ext] theorem ext {f g : Tensor K ι} (h : ∀ x, f x = g x) : f = g := funext h

/-- Pull a signature along an explicit port bijection. -/
def reindex (e : ι ≃ κ) (f : Tensor K ι) : Tensor K κ :=
  fun x => f (fun i => x (e i))

@[simp] theorem reindex_apply (e : ι ≃ κ) (f : Tensor K ι) (x : κ → Bool) :
    reindex e f x = f (fun i => x (e i)) := rfl

@[simp] theorem reindex_refl (f : Tensor K ι) : reindex (Equiv.refl ι) f = f := rfl

@[simp] theorem reindex_trans (e : ι ≃ κ) (d : κ ≃ ν) (f : Tensor K ι) :
    reindex d (reindex e f) = reindex (e.trans d) f := rfl

@[simp] theorem reindex_symm (e : ι ≃ κ) (f : Tensor K ι) :
    reindex e.symm (reindex e f) = f := by
  funext x
  simp [reindex]

end Tensor

namespace Signature

variable {K : Type*} {n : ℕ}

/-- Insert a bit as the first port. All remaining ports retain their order. -/
def pin (f : Signature K (n + 1)) (b : Bool) : Signature K n :=
  fun x => f (Fin.cons b x)

@[simp] theorem pin_apply (f : Signature K (n + 1)) (b : Bool) (x : Fin n → Bool) :
    pin f b x = f (Fin.cons b x) := rfl

/-- A nullary signature retains its scalar; it is not normalized away. -/
def scalar (c : K) : Signature K 0 := fun _ => c

@[simp] theorem scalar_apply (c : K) (x : Fin 0 → Bool) : scalar c x = c := rfl

end Signature
end Holant
